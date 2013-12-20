from datetime import date, datetime
import decimal
import os
import pytz
import re
import tempfile
import traceback

from django.conf import settings
from django.contrib.auth.models import User
from django.core.exceptions import ValidationError
from django.core.exceptions import PermissionDenied
from django.core.files.storage import get_storage_class
from django.core.mail import mail_admins
from django.core.servers.basehttp import FileWrapper
from django.db import IntegrityError
from django.db import transaction
from django.db.models.signals import pre_delete
from django.http import HttpResponse, HttpResponseNotFound, \
    StreamingHttpResponse
from django.shortcuts import get_object_or_404
from django.utils.translation import ugettext as _
from django.utils import timezone
from modilabs.utils.subprocess_timeout import ProcessTimedOut
from pyxform.errors import PyXFormError
from pyxform.xform2json import create_survey_element_from_xml
import sys
import common_tags

from odk_logger.models import Attachment
from odk_logger.models import Instance
from odk_logger.models.instance import InstanceHistory
from odk_logger.models.instance import get_id_string_from_xml_str
from odk_logger.models import XForm
from odk_logger.models.xform import XLSFormError
from odk_logger.xform_instance_parser import InstanceInvalidUserError, \
    IsNotCrowdformError, DuplicateInstance, clean_and_parse_xml, \
    get_uuid_from_xml, get_deprecated_uuid_from_xml, \
    get_submission_date_from_xml
from odk_viewer.models.parsed_instance import _remove_from_mongo
from odk_viewer.models.parsed_instance import xform_instances

from odk_viewer.models import ParsedInstance, DataDictionary
from utils.model_tools import queryset_iterator, set_uuid
from xml.dom import Node


OPEN_ROSA_VERSION_HEADER = 'X-OpenRosa-Version'
HTTP_OPEN_ROSA_VERSION_HEADER = 'HTTP_X_OPENROSA_VERSION'
OPEN_ROSA_VERSION = '1.0'
DEFAULT_CONTENT_TYPE = 'text/xml; charset=utf-8'
DEFAULT_CONTENT_LENGTH = settings.DEFAULT_CONTENT_LENGTH

uuid_regex = re.compile(r'<formhub><uuid>([^<]+)</uuid></formhub>',
                        re.DOTALL)

mongo_instances = settings.MONGO_DB.instances

@transaction.commit_on_success
def _save_media_files (instance, media_files):
    """Create an Attachment object for each media file, and
    associate it with the given Instance object"""

    for f in media_files:
        Attachment.objects.get_or_create(instance=instance,
                                         media_file=f,
                                         mimetype=f.content_type)

@transaction.commit_on_success
def _generate_new_instance (user, xml, media_files, status):
    """Create and return a new Instance object for this user and xml data combination,
    or None if the transaction fails"""

    instance = Instance.objects.create(xml=xml,
                                       user=user,
                                       status=status)
    if len(media_files) > 0:
        _save_media_files (instance, media_files)

    return instance

@transaction.commit_on_success
def _update_existing_instance (instance_uuid, user, xml, media_files, status):
    """Update the prior Instance for this xml data by changing its uuid
    (not ideal, but we want to be compatible with the rest of the system
    for now), and create a new InstanceHistory object for the prior version.

    If the update succeeds, it returns the Instance object that was changed,
    or None"""

    try:
        # legacy logic assumes that there will be just one existing
        # Instance object per uuid, so instead of doing filter() and
        # grabbing the [0] slice, we're just going to do a get()
        instance = Instance.objects.get(uuid=instance_uuid)

        # create an InstanceHistory object
        InstanceHistory.objects.create(xml=instance.xml,
                                       xform_instance=instance,
                                       uuid=instance_uuid)

        # and update the previously-existing Instance object
        # (ugly: the updated instance uuid is in the xml)
        new_instance_uuid = get_uuid_from_xml(xml)
        if new_instance is None:
            raise ValueError(_("XML string must have an instanceID"))
        else:
            instance.xml = xml
            instance.uuid = new_instance_uuid
            instance.save()

        if len(media_files) > 0:
            _save_media_files (instance, media_files)

        return instance

    except (Instance.MultipleObjectsReturned, Instance.DoesNotExist):
        pass

@transaction.commit_on_success
def _override_date_created (instance, xml, date_created_override):
    """Over-ride the instance creation date if it was passed in as an
    explicit parameter, or if it was found in the xml data"""

    if date_created_override is None:
        date_created_override = get_submission_date_from_xml(xml)

    if date_created_override is not None:

        # stet from legacy code here:
        # reset the timezone to utc if necessary
        try:
            if not timezone.is_aware(date_created_override):
                date_created_override = timezone.make_aware(date_created_override,
                                                            timezone.utc)

            instance.date_created = date_created_override
            instance.save()
        except Exception:
            # according to the django docs, there are cases where
            # calling timezone.make_aware() can raise an exception
            # if value doesn't exist or is ambiguous because of DST transitions
            pass

@transaction.commit_on_success
def _generate_parsed_instance (instance):
    """Get or Create the ParsedInstance object for this Instance,
    and return it if successful, or None otherwise"""

    if instance.xform is not None:
        pi, created = ParsedInstance.objects.get_or_create(instance=instance)
        return pi

def _fetch_xform (uuid, id_string, username):
    """Find and return the XForm object which matches either:

    (a) The given XForm uuid (preferred case); or
    (b) The id_string/username combination

    returning None if the XForm does not exist, or raising
    a duplicate XForm exception if more than one XForm exists
    for either retrieval method (a) or (b)
    """

    try:
        # attempt to get the XForm by its uuid: this is the "ideal" method
        return XForm.objects.get(uuid=uuid)
    except XForm.MultipleObjectsReturned:
        raise ValueError(_("Duplicate XForm"))
    except XForm.DoesNotExist:
        # try instead using the id_string/username combination
        try:
            return XForm.objects.get(id_string=id_string, user__username=username)
        except XForm.MultipleObjectsReturned:
            raise ValueError(_("Duplicate XForm"))
        except XForm.DoesNotExist:
            pass

def create_instance(username,
                    xml_file,
                    media_files,
                    status=u'submitted_via_web',
                    uuid=None, # this is the XForm uuid
                    date_created_override=None,
                    request=None):
    """Create a new Instance object (and ParsedInstance object) for this xml data and User
    combination if valid, saving any media files as Attachment objects.

    Despite its name, this function will also *update* an existing Instance, depending on
    whether or not it finds a 'deprecatedID' within the xml data, by storing its current
    version as an InstanceHistory object, then generating a brand-new Instance object.

    If successful, this function returns the Instance object.

    Unlike prior versions, which accepted form submissions missing either usernames, XForm uuids,
    or both, this version requires that at least the username or XForm uuid be defined.

    The XForm uuid is allowed to be missing from the function parameters, but in that case it must
    exist in the xml, as defined by the uuid_regex pattern.

    Otherwise, the XForm must be retrievable by its id_string/username combination,
    or the submission will fail.
    """

    try:
        xml = xml_file.read()
    except IOError:
        xml = None

    # if the XForm uuid is not passed in as a parameter,
    # try to find it in the xml data instead (this is how
    # ODK submissions arrive)

    if uuid is None:
        try:
            uuid = uuid_regex.split(xml)[1]
        except (TypeError, IndexError):
            pass

    if username is None and uuid is None:
        raise InstanceInvalidUserError()

    # see if we can determine the XForm
    # corresponding to this form submission

    xform = _fetch_xform (uuid,
                          get_id_string_from_xml_str(xml),
                          username.lower())
    if xform is None:
        raise ValueError(_("No such XForm"))
    
    # check the XForm permissions:
    # crowdforms can be submitted by anyone,
    # but non-crowdforms must have the correct User

    if not xform.is_crowd_form:

        # make sure that if the XForm requires authentication
        # this User is logged in, and matches the XForm's owner

        if xform.user.profile.require_auth \
           and xform.user != request.user:
            raise PermissionDenied(
                _(u"%(request_user)s is not allowed to make submissions "
                  u"to %(form_user)s's %(form_title)s form." % {
                      'request_user': request.user,
                      'form_user': xform.user,
                      'form_title': xform.title}))

        # even if the User who owns the XForm does not require
        # authentication, we need to make sure that this User
        # is indeed the XForm owner, otherwise raise an error

        if username.lower() != xform.user.username.lower():
            raise IsNotCrowdformError()

    # crowdform submissions have the username='crowdform' (literally)
    # so need to change the username to the XForm owner's username

    if xform.is_crowd_form:
        username = xform.user.username

    # finally, before using this xml data to create/update an Instance,
    # make sure the User object for this username actually exists

    user = get_object_or_404(User, username=username.lower()) # raise Http404 if not found

    if Instance.objects.filter(xml=xml, user=user).count() > 0:
        raise DuplicateInstance()
    else:
        instance = None

        # determine whether or not this xml corresponds
        # to an update of an existing Instance, or not

        deprecated_instance_uuid = get_deprecated_uuid_from_xml(xml)
        if deprecated_instance_uuid is not None \
           and Instance.objects.filter(uuid=deprecated_instance_uuid).count() > 0:
            # legacy logic: the instance to update will always be
            # the first one for this filter...
            deprecated_instance = Instance.objects.filter(uuid=deprecated_instance_uuid)[0]
            instance = _update_existing_instance (deprecated_instance_uuid,
                                                  user,
                                                  xml,
                                                  media_files,
                                                  status)
        if instance is None:
            instance = _generate_new_instance (user, xml, media_files, status)

        if instance is not None:
            _override_date_created (instance, xml, date_created_override)

            # stet of legacy code that doesn't make sense on the surface:
            # the create part of get_or_create() automatically saves the
            # newly-created object, and django is synchronous by default,
            # so passing async=False doesn't seem to be needed here

            parsed_instance = _generate_parsed_instance (instance)
            if parsed_instance is not None:
                parsed_instance.save(async=False)

        return instance


def report_exception(subject, info, exc_info=None):
    if exc_info:
        cls, err = exc_info[:2]
        message = _(u"Exception in request:"
                    u" %(class)s: %(error)s")\
            % {'class': cls.__name__, 'error': err}
        message += u"".join(traceback.format_exception(*exc_info))
    else:
        message = u"%s" % info

    if settings.DEBUG or settings.TESTING_MODE:
        sys.stdout.write("Subject: %s\n" % subject)
        sys.stdout.write("Message: %s\n" % message)
    else:
        mail_admins(subject=subject, message=message)

def response_with_mimetype_and_name(
        mimetype, name, extension=None, show_date=True, file_path=None,
        use_local_filesystem=False, full_mime=False):
    if extension is None:
        extension = mimetype
    if not full_mime:
        mimetype = "application/%s" % mimetype
    if file_path:
        try:
            if not use_local_filesystem:
                default_storage = get_storage_class()()
                wrapper = FileWrapper(default_storage.open(file_path))
                response = StreamingHttpResponse(wrapper, mimetype=mimetype)
                response['Content-Length'] = default_storage.size(file_path)
            else:
                wrapper = FileWrapper(open(file_path))
                response = StreamingHttpResponse(wrapper, mimetype=mimetype)
                response['Content-Length'] = os.path.getsize(file_path)
        except IOError:
            response = HttpResponseNotFound(
                _(u"The requested file could not be found."))
    else:
        response = HttpResponse(mimetype=mimetype)
    response['Content-Disposition'] = disposition_ext_and_date(
        name, extension, show_date)
    return response


def disposition_ext_and_date(name, extension, show_date=True):
    if name is None:
        return 'attachment;'
    if show_date:
        name = "%s_%s" % (name, date.today().strftime("%Y_%m_%d"))
    return 'attachment; filename=%s.%s' % (name, extension)


def store_temp_file(data):
    tmp = tempfile.TemporaryFile()
    ret = None
    try:
        tmp.write(data)
        tmp.seek(0)
        ret = tmp
    finally:
        tmp.close()
    return ret


def publish_form(callback):
    try:
        return callback()
    except (PyXFormError, XLSFormError) as e:
        return {
            'type': 'alert-error',
            'text': e
        }
    except IntegrityError as e:
        return {
            'type': 'alert-error',
            'text': _(u'Form with this id or SMS-keyword already exists.'),
        }
    except ValidationError as e:
        # on clone invalid URL
        return {
            'type': 'alert-error',
            'text': _(u'Invalid URL format.'),
        }
    except AttributeError as e:
        # form.publish returned None, not sure why...
        return {
            'type': 'alert-error',
            'text': e
        }
    except ProcessTimedOut as e:
        # catch timeout errors
        return {
            'type': 'alert-error',
            'text': _(u'Form validation timeout, please try again.'),
        }
    except Exception, e:
        # error in the XLS file; show an error to the user
        return {
            'type': 'alert-error',
            'text': e
        }


def publish_xls_form(xls_file, user, id_string=None):
    """ Creates or updates a DataDictionary with supplied xls_file,
        user and optional id_string - if updating
    """
    # get or create DataDictionary based on user and id string
    if id_string:
        dd = DataDictionary.objects.get(
            user=user, id_string=id_string)
        dd.xls = xls_file
        dd.save()
        return dd
    else:
        return DataDictionary.objects.create(
            user=user,
            xls=xls_file
        )


def publish_xml_form(xml_file, user, id_string=None):
    xml = xml_file.read()
    survey = create_survey_element_from_xml(xml)
    form_json = survey.to_json()
    if id_string:
        dd = DataDictionary.objects.get(user=user, id_string=id_string)
        dd.xml = xml
        dd.json = form_json
        dd._mark_start_time_boolean()
        set_uuid(dd)
        dd._set_uuid_in_xml()
        dd.save()
        return dd
    else:
        dd = DataDictionary(user=user, xml=xml, json=form_json)
        dd._mark_start_time_boolean()
        set_uuid(dd)
        dd._set_uuid_in_xml(file_name=xml_file.name)
        dd.save()
        return dd


class BaseOpenRosaResponse(HttpResponse):
    status_code = 201

    def __init__(self, *args, **kwargs):
        super(BaseOpenRosaResponse, self).__init__(*args, **kwargs)

        self[OPEN_ROSA_VERSION_HEADER] = OPEN_ROSA_VERSION
        tz = pytz.timezone(settings.TIME_ZONE)
        dt = datetime.now(tz).strftime('%a, %d %b %Y %H:%M:%S %Z')
        self['Date'] = dt
        self['X-OpenRosa-Accept-Content-Length'] = DEFAULT_CONTENT_LENGTH
        self['Content-Type'] = DEFAULT_CONTENT_TYPE


class OpenRosaResponse(BaseOpenRosaResponse):
    status_code = 201

    def __init__(self, *args, **kwargs):
        super(OpenRosaResponse, self).__init__(*args, **kwargs)
        # wrap content around xml
        self.content = '''<?xml version='1.0' encoding='UTF-8' ?>
<OpenRosaResponse xmlns="http://openrosa.org/http/response">
        <message nature="">%s</message>
</OpenRosaResponse>''' % self.content


class OpenRosaResponseNotFound(OpenRosaResponse):
    status_code = 404


class OpenRosaResponseBadRequest(OpenRosaResponse):
    status_code = 400


class OpenRosaResponseNotAllowed(OpenRosaResponse):
    status_code = 405


def inject_instanceid(xml_str, uuid):
    if get_uuid_from_xml(xml_str) is None:
        xml = clean_and_parse_xml(xml_str)
        children = xml.childNodes
        if children.length == 0:
            raise ValueError(_("XML string must have a survey element."))

        # check if we have a meta tag
        survey_node = children.item(0)
        meta_tags = [
            n for n in survey_node.childNodes
            if n.nodeType == Node.ELEMENT_NODE
            and n.tagName.lower() == "meta"]
        if len(meta_tags) == 0:
            meta_tag = xml.createElement("meta")
            xml.documentElement.appendChild(meta_tag)
        else:
            meta_tag = meta_tags[0]

        # check if we have an instanceID tag
        uuid_tags = [
            n for n in meta_tag.childNodes
            if n.nodeType == Node.ELEMENT_NODE
            and n.tagName == "instanceID"]
        if len(uuid_tags) == 0:
            uuid_tag = xml.createElement("instanceID")
            meta_tag.appendChild(uuid_tag)
        else:
            uuid_tag = uuid_tags[0]
        # insert meta and instanceID
        text_node = xml.createTextNode(u"uuid:%s" % uuid)
        uuid_tag.appendChild(text_node)
        return xml.toxml()
    return xml_str


def update_mongo_for_xform(xform, only_update_missing=True):
    instance_ids = set(
        [i.id for i in Instance.objects.only('id').filter(xform=xform)])
    sys.stdout.write("Total no of instances: %d\n" % len(instance_ids))
    mongo_ids = set()
    user = xform.user
    userform_id = "%s_%s" % (user.username, xform.id_string)
    if only_update_missing:
        sys.stdout.write("Only updating missing mongo instances\n")
        mongo_ids = set(
            [rec[common_tags.ID] for rec in mongo_instances.find(
                {common_tags.USERFORM_ID: userform_id},
                {common_tags.ID: 1})])
        sys.stdout.write("Total no of mongo instances: %d\n" % len(mongo_ids))
        # get the difference
        instance_ids = instance_ids.difference(mongo_ids)
    else:
        # clear mongo records
        mongo_instances.remove({common_tags.USERFORM_ID: userform_id})
    # get instances
    sys.stdout.write(
        "Total no of instances to update: %d\n" % len(instance_ids))
    instances = Instance.objects.only('id').in_bulk(
        [id for id in instance_ids])
    total = len(instances)
    done = 0
    for id, instance in instances.items():
        (pi, created) = ParsedInstance.objects.get_or_create(instance=instance)
        pi.save(async=False)
        done += 1
        # if 1000 records are done, flush mongo
        if (done % 1000) == 0:
            sys.stdout.write(
                'Updated %d records, flushing MongoDB...\n' % done)
        settings.MONGO_CONNECTION.admin.command({'fsync': 1})
        progress = "\r%.2f %% done..." % ((float(done) / float(total)) * 100)
        sys.stdout.write(progress)
        sys.stdout.flush()
    # flush mongo again when done
    settings.MONGO_CONNECTION.admin.command({'fsync': 1})
    sys.stdout.write(
        "\nUpdated %s\n------------------------------------------\n"
        % xform.id_string)


def mongo_sync_status(remongo=False, update_all=False, user=None, xform=None):
    """Check the status of records in the mysql db versus mongodb. At a
    minimum, return a report (string) of the results.

    Optionally, take action to correct the differences, based on these
    parameters, if present and defined:

    remongo    -> if True, update the records missing in mongodb (default: False)
    update_all -> if True, update all the relevant records (default: False)
    user       -> if specified, apply only to the forms for the given user (default: None)
    xform      -> if specified, apply only to the given form (default: None)

    """

    qs = XForm.objects.only('id_string', 'user').select_related('user')
    if user and not xform:
        qs = qs.filter(user=user)
    elif user and xform:
        qs = qs.filter(user=user, id_string=xform.id_string)
    else:
        qs = qs.all()

    total = qs.count()
    found = 0
    done = 0
    total_to_remongo = 0
    report_string = ""
    for xform in queryset_iterator(qs, 100):
        # get the count
        user = xform.user
        instance_count = Instance.objects.filter(xform=xform).count()
        userform_id = "%s_%s" % (user.username, xform.id_string)
        mongo_count = mongo_instances.find(
            {common_tags.USERFORM_ID: userform_id}).count()

        if instance_count != mongo_count or update_all:
            line = "user: %s, id_string: %s\nInstance count: %d\t"\
                   "Mongo count: %d\n---------------------------------"\
                   "-----\n" % (
                       user.username, xform.id_string, instance_count,
                       mongo_count)
            report_string += line
            found += 1
            total_to_remongo += (instance_count - mongo_count)

            # should we remongo
            if remongo or (remongo and update_all):
                if update_all:
                    sys.stdout.write(
                        "Updating all records for %s\n--------------------"
                        "---------------------------\n" % xform.id_string)
                else:
                    sys.stdout.write(
                        "Updating missing records for %s\n----------------"
                        "-------------------------------\n"
                        % xform.id_string)
                update_mongo_for_xform(
                    xform, only_update_missing=not update_all)
        done += 1
        sys.stdout.write(
            "%.2f %% done ...\r" % ((float(done) / float(total)) * 100))
    # only show stats if we are not updating mongo, the update function
    # will show progress
    if not remongo:
        line = "Total # of forms out of sync: %d\n" \
            "Total # of records to remongo: %d\n" % (
            found, total_to_remongo)
        report_string += line
    return report_string


def remove_xform(xform):
    # disconnect parsed instance pre delete signal
    pre_delete.disconnect(_remove_from_mongo, sender=ParsedInstance)

    # delete instances from mongo db
    query = {
        ParsedInstance.USERFORM_ID:
        "%s_%s" % (xform.user.username, xform.id_string)}
    xform_instances.remove(query, j=True)

    # delete xform, and all related models
    xform.delete()

    # reconnect parsed instance pre delete signal?
    pre_delete.connect(_remove_from_mongo, sender=ParsedInstance)
