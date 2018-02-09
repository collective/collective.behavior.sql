import logging
import traceback
import datetime
import base64
import sys
from ast import literal_eval
from unidecode import unidecode
from OFS.SimpleItem import SimpleItem
from AccessControl import ClassSecurityInfo
from plone.dexterity.utils import safe_utf8
from zope.schema.vocabulary import SimpleTerm
from zope.schema.vocabulary import SimpleVocabulary
from zope.interface import providedBy, implements, implementer,  Interface, directlyProvidedBy
from zope import component, interface, schema
from zope.annotation.interfaces import IAnnotations
from Products.CMFCore.utils import getToolByName
from zope.component.hooks import getSite
from plone.app.textfield.interfaces import IRichText
from plone.app.textfield.value import RichTextValue
from plone.uuid.interfaces import IUUID, ATTRIBUTE_NAME
from plone.app.uuid.utils import uuidToObject
from plone.namedfile.interfaces import INamedBlobImage
from plone.dexterity.content import Item, _marker, _zone
from z3c.relationfield.interfaces import IRelationValue
from z3c.relationfield.relation import create_relation, RelationValue, _path, _interfaces_flattened
from z3c.relationfield.interfaces import IRelationChoice, IRelationList, ITemporaryRelationValue
from plone.dexterity.browser.traversal import DexterityPublishTraverse
from zope.publisher.interfaces import IPublishTraverse
from zope.interface.adapter import AdapterRegistry
from zope.interface import providedBy
from collective.behavior.sql.behavior.schemaeditor import IFieldSQLBehavior
from collective.behavior.sql import _
from collective.behavior.sql.interfaces import ISQLDexterityItem, ISQLBaseConnectionUtility, ISQLConnectionsUtility
from collective.behavior.sql.interfaces import ISQLTypeSettings, ISQLItemPublisher
from collective.behavior.sql.interfaces import ICollectiveBehaviorSQLLayer, ISQLTypeSchemaContext, ISQLTraverser
from plone.dexterity.interfaces import IDexterityFTI
from plone.dexterity.utils import datify, iterSchemataForType
from DateTime import DateTime
from plone.memoize.view import memoize
from Products.CMFCore import permissions
from zope.component import getUtility, queryUtility, adapter, getMultiAdapter, queryMultiAdapter, getGlobalSiteManager, provideAdapter
from zope.component.interfaces import IFactory
from zope.publisher.interfaces.browser import IBrowserPublisher, IBrowserRequest, IBrowserView
from zope.sqlalchemy import ZopeTransactionExtension, register
from zope.i18n import translate
from zope.container.interfaces import INameChooser
from zope.keyreference.interfaces import IKeyReference
from zope.intid.interfaces import IIntIds
from plone.i18n.normalizer.interfaces import IURLNormalizer
from plone.app.content.interfaces import INameFromTitle
from zope.i18nmessageid import MessageFactory
from sqlalchemy.ext.declarative import declarative_base
from sqlalchemy.ext.automap import automap_base
from sqlalchemy.orm import scoped_session, sessionmaker, relation, exc as orm_exc
from sqlalchemy import create_engine, MetaData, Table, text
from sqlalchemy.engine import reflection
from sqlalchemy.inspection import inspect
from sqlalchemy.ext.automap import generate_relationship
from zope.component import getAllUtilitiesRegisteredFor
from plone.namedfile.interfaces import INamedImage
from plone.namedfile.interfaces import INamedFile
from plone.namedfile.file import NamedBlobImage, NamedFile, NamedImage
from zope.schema.fieldproperty import FieldProperty
from zope.schema.interfaces import ITuple, IList, IDatetime
LOG = logging.getLogger(__name__)

SpecificAttrs = ['unindexObject', 'opaqueValues', 'getPhysicalPath', 'getId', 'indexObject', 'getPortalTypeName', 'portal_type']

class SQLRelationValue(object):
    implements(ITemporaryRelationValue, IKeyReference)
    
    key_type_id = 'sqlrelationvalue'

    def __init__(self, portal_type, uid, from_object=None):
        self.portal_type = portal_type
        self.to_id = 0
        self.uid = uid
        # these will be set automatically by events
        self.from_object = from_object
        self.__parent__ = None
        self.from_attribute = None

    @property
    def from_id(self):
        intids = getUtility(IIntIds)
        return intids.getId(self.from_object)

    @property
    def from_path(self):
        path = _path(self.from_object)
        return path

    @property
    def from_interfaces(self):
        return providedBy(self.from_object)

    @property
    def from_interfaces_flattened(self):
        return _interfaces_flattened(self.from_interfaces)

    @property
    def to_object(self):
        catalog = getToolByName(getSite(), 'portal_catalog')
        brains = catalog.unrestrictedSearchResults(portal_type=self.portal_type, UID=self.uid)
        for brain in brains:
            obj = brain.getObject()
            return obj
        return None

    @property
    def to_path(self):
        if self.to_object is None:
            return self._broken_to_path
        return _path(self.to_object)

    @property
    def to_interfaces(self):
        return providedBy(self.to_object)

    @property
    def to_interfaces_flattened(self):
        return _interfaces_flattened(self.to_interfaces)

    def __eq__(self, other):
        if not isinstance(other, RelationValue):
            return False
        self_sort_key = self._sort_key()
        other_sort_key = other._sort_key()
        # if one of the relations we are comparing doesn't have a source
        # yet, only compare targets. This is to make comparisons within
        # ChoiceWidget work; a stored relation would otherwise not compare
        # equal with a relation generated for presentation in the UI
        if self_sort_key[0] is None or other_sort_key[0] is None:
            return self_sort_key[-1] == other_sort_key[-1]
        # otherwise do a full comparison
        return self_sort_key == other_sort_key

    def __ne__(self, other):
        return not self.__eq__(other)

    def __cmp__(self, other):
        if not hasattr(other, '_sort_key'):
            return cmp(self._sort_key(), None)
        return cmp(self._sort_key(), other._sort_key())

    def _sort_key(self):
        return (self.from_attribute, self.from_path, self.to_path)

    def broken(self, to_path):
        self._broken_to_path = to_path
        self.uid = None

    def isBroken(self):
        return self.uid is None


@implementer(ISQLDexterityItem)
class SQLDexterityItem(Item):

    security = ClassSecurityInfo()

    def __init__(
            self, sql_id=None, sql_virtual=False, sql_item=None,
            id=None, title=_marker, subject=_marker, description=_marker,
            contributors=_marker, effective_date=_marker,
            expiration_date=_marker, format=_marker, language=_marker,
            rights=_marker, **kwargs):
        connection = None
        if kwargs.get('portal_type'):
            self.portal_type = kwargs.get('portal_type')
            connection = self.getConnection()
        self.sql_id = str(sql_id)
        self.sql_virtual = sql_virtual
        self._v_sql_item = sql_item
        if not connection or ('creation_date' not in connection.fieldnames.keys() and 'modification_date' not in connection.fieldnames.keys()):
            super(SQLDexterityItem, self).__init__(
                id=id, title=title, subject=subject, description=description,
                contributors=contributors, effective_date=effective_date,
                expiration_date=expiration_date, format=format, language=language,
                rights=rights, **kwargs)
        else:
            if id is not None:
                self.id = id
#            self._v_sql_item = self.getSQLItem()
            now = DateTime()
            dt_now = datetime.datetime.now()
            if 'creation_date' in connection.fieldnames.keys():
                self.creation_date = getattr(self, 'creation_date', dt_now)
            else:
                self.creation_date = now
            if 'modification_date' in connection.fieldnames.keys():
                self.modification_date = getattr(self, 'modification_date', dt_now)
            else:
                self.modification_date = now

            if title is not _marker:
                self.setTitle(title)
            if subject is not _marker:
                self.setSubject(subject)
            if description is not _marker:
                self.setDescription(description)
            if contributors is not _marker:
                self.setContributors(contributors)
            if effective_date is not _marker:
                self.setEffectiveDate(effective_date)
            if expiration_date is not _marker:
                self.setExpirationDate(expiration_date)
            if format is not _marker:
                self.setFormat(format)
            if language is not _marker:
                self.setLanguage(language)
            if rights is not _marker:
                self.setRights(rights)
            for (k, v) in kwargs.items():
                setattr(self, k, v)
        
    def sqlAdd(self):
        data = {}
        connection = self.getConnection()
        if connection:
            for k,v in connection.fieldnames.items():
                data[v] = getattr(self, k, None)
            self.sql_id = connection.add(**data)
    
    def getConnection(self):
        connection = queryUtility(ISQLConnectionsUtility, name=self.portal_type, default=None)
        if connection == None and self.portal_type:
            fti = queryUtility(IDexterityFTI, name=self.portal_type, default=None)
            if not fti:
                return None
            updateConnectionsForFti(fti)
            connection = queryUtility(ISQLConnectionsUtility, name=self.portal_type, default=None)
        return connection

    def getRawSQLItem(self):
        if not self.sql_id:
            return None

        connection = self.getConnection()
        options = {}
        try:
            sql_id = int(self.sql_id)
        except:
            sql_id = self.sql_id
        options[connection.sql_id_column] = sql_id
        sql_items = connection.query(**options)
        if sql_items:
            return sql_items[0]
        return None

    def getSQLItem(self):
        if not self.sql_id:
            return None
        try:
            if not self._v_sql_item:
                self._v_sql_item = self.getRawSQLItem()
        except:
            self._v_sql_item = self.getRawSQLItem()
        return self._v_sql_item

    def getSQLItemValue(self, name):
        value = None
        connection = self.getConnection()
        if connection and name in connection.fieldnames.keys():
            sql_column = connection.fieldnames[name]
            sql_item = self.getSQLItem()
            try:
                sql_id = getattr(sql_item, connection.sql_id_column, None)
            except orm_exc.DetachedInstanceError:
                self._v_sql_item = None
                sql_item = self.getSQLItem()
                sql_id = getattr(sql_item, connection.sql_id_column, None)
            fieldname = 'name'
            if sql_item and sql_column:
                while '.' in sql_column:
                    sql_key = sql_column.split('.')[0]
                    sql_item = getattr(sql_item, sql_key, None)
                    if isinstance(sql_item, list):
                        value = sql_item
                        fieldname = sql_column.split('.')[-1]
                        break
                    sql_column = '.'.join(sql_column.split('.')[1:])
                else:
                    if not isinstance(sql_item, list):
                        value = getattr(sql_item, sql_column, None)
        return value

    def opaqueValues(self):
        return []

    def __getattr__(self, name):
        if name.startswith('_') or name.startswith('portal_') or name.startswith('@@') or name in SpecificAttrs:
            return super(SQLDexterityItem, self).__getattr__(name)
        value = super(SQLDexterityItem, self).__getattr__(name)
        if isinstance(value, unicode) and '/' in str(value):
            # this might be an URL saved as default of a field in the schemaeditor.
            # URLs must be strings otherwise it will brake further!
            return str(value)
        return value
    
    def __getattribute__(self, name):
        if name.startswith('_') or name.startswith('portal_') or name.startswith('@@') or name == 'sql_id' or name in SpecificAttrs:
            return super(SQLDexterityItem, self).__getattribute__(name)
        connection = queryUtility(ISQLConnectionsUtility, name=self.portal_type, default=None)
        if connection == None and self.portal_type:
            fti = queryUtility(IDexterityFTI, name=self.portal_type, default=None)
            if not fti:
                return None
            updateConnectionsForFti(fti)
            connection = queryUtility(ISQLConnectionsUtility, name=self.portal_type, default=None)
        if name == 'view':
            #be sure session and sqlitem are up to date
            self._v_sql_item = None
            connection.session.close()
        if not connection:
            return super(SQLDexterityItem, self).__getattribute__(name)
        if name == 'UID' and self.sql_virtual:
            return self.portal_type+'-'+connection.sql_table+'-'+str(self.sql_id)
        if name == 'id' and 'id' not in connection.fieldnames.keys():
            if not self.sql_virtual:
                return super(SQLDexterityItem, self).__getattribute__(name)
            fti = ISQLTypeSettings(getUtility(IDexterityFTI, name=self.portal_type))
            nameFromTitle = INameFromTitle(self, None)
            if nameFromTitle is not None and nameFromTitle.title:
                sql_folder_id = getattr(fti, 'sql_folder_id', 'data-'+self.portal_type)
                title = nameFromTitle.title
                folder = None
                if IRelationValue.providedBy(sql_folder_id):
                    folder = sql_folder_id.to_object
                elif sql_folder_id and sql_folder_id.startswith('/'):
                    portal = getToolByName(getSite(), 'portal_url').getPortalObject()
                    folder = portal.restrictedTraverse(sql_folder_id)
                if folder:
                    name = INameChooser(folder).chooseName(title, self)
                    return name
#                return INameChooser(getSite()).chooseName(title, self)
#                return getUtility(IURLNormalizer).normalize(title)
                return self.sql_id
        if name in connection.fieldnames.keys():
            sql_column = connection.fieldnames[name]
            sql_item = self.getSQLItem()
            try:
                sql_id = getattr(sql_item, connection.sql_id_column, None)
            except orm_exc.DetachedInstanceError:
                self._v_sql_item = None
                sql_item = self.getSQLItem()
                sql_id = getattr(sql_item, connection.sql_id_column, None)
            fieldname = 'name'
            if sql_item and sql_column:
                while '.' in sql_column:
                    sql_key = sql_column.split('.')[0]
                    sql_item = getattr(sql_item, sql_key, None)
                    if isinstance(sql_item, list):
                        value = sql_item
                        fieldname = sql_column.split('.')[-1]
                        break
                    sql_column = '.'.join(sql_column.split('.')[1:])
                else:
                    if not isinstance(sql_item, list):
                        value = getattr(sql_item, sql_column, None)
                if not value and (isinstance(value, list) or hasattr(value, '_sa_instance_state')):
                    value = ''
                elif (isinstance(value, list) or hasattr(value, '_sa_instance_state')):
                    sqlftis = [a for a in getAllUtilitiesRegisteredFor(IDexterityFTI) if 'collective.behavior.sql.behavior.behaviors.ISQLContent' in a.behaviors and getattr(a, 'sql_table', None)]
                    if name == 'subject':
                        return tuple([getattr(a, fieldname, '') for a in value])
                    tableftis = []
                    for iface in iterSchemataForType(self.portal_type):
                        if name in iface.names():
                            field = iface[name]
                            if IRelationChoice.providedBy(field) or IRelationList.providedBy(field):
                                if IRelationChoice.providedBy(field):
                                    allowed_types = field.source.query.get('portal_type', [])
                                else:
                                    allowed_types = field.value_type.source.query.get('portal_type', [])
                                tableftis = []
                                for sqlfti in sqlftis:
                                    adapted = ISQLTypeSettings(sqlfti, None)
                                    if isinstance(value, list):
                                        classname = value[0].__class__.__name__
                                    else:
                                        classname = value.__class__.__name__
                                    if adapted and getattr(adapted, 'sql_table', None) == classname:
                                        if not allowed_types or sqlfti.id in allowed_types:
                                            tableftis.append(adapted)
                                catalog = getToolByName(getSite(), 'portal_catalog')
                                relations = []
                                for tablefti in tableftis:
                                    sql_id_column = getattr(tablefti, 'sql_id_column', 'id')
                                    valueids = []
                                    if isinstance(value, list):
                                        valueids = [getattr(a, sql_id_column, None) for a in value if getattr(a, sql_id_column, None)]
                                    else:
                                        valueids = getattr(value, sql_id_column, None)
                                    valueids = [str(a) for a in valueids]
                                    brains = catalog.unrestrictedSearchResults(portal_type=tablefti.id, sql_id=valueids)
                                    for brain in brains:
                                        relations.append(SQLRelationValue(brain.portal_type, brain.UID, self))
                                if IRelationChoice.providedBy(field) and relations:
                                    return relations[0]
                                elif IRelationList.providedBy(field) and relations:
                                    return relations
                            elif ITuple.providedBy(field):
                                return tuple([getattr(a, fieldname, '') for a in value])
                            elif IList.providedBy(field):
                                return [getattr(a, fieldname, '') for a in value]
                            elif value and isinstance(value, list):
                                value = getattr(value[0], fieldname, '')
                for iface in iterSchemataForType(self.portal_type):
                    if name == 'subject':
                        try:
                            return tuple([a.decode('utf-8') for a in literal_eval(value)])
                        except:
                            return tuple([a.strip() for a in value.split(',')])
                    if name in iface.names():
                        field = iface[name]
                        if IRichText.providedBy(field):
                            if not value:
                                value = ''
                            if not '<p' in value or not '<br' in value:
                                value = '<p>'+'</p><p>'.join([a for a in value.split('\n') if a.strip()])+'</p>'
#                            try:
#                                value = str(value)
#                            except:
#                                try:
#                                    value = value.decode('utf-8')
#                                except:
#                                    try:
#                                        value = value.encode('utf-8')
#                                    except:
#                                        pass
                            return RichTextValue(unidecode(value))
                        elif INamedBlobImage.providedBy(field):
                            return NamedBlobImage(base64.b64decode(value), filename=unicode(self.portal_type+self.id+".jpg"))
                        elif ITuple.providedBy(field):
                            if not value:
                                return tuple([])
                            try:
                                return tuple([a.decode('utf-8') for a in literal_eval(value)])
                            except:
                                return tuple([a.strip() for a in value.split(',')])
                        elif IList.providedBy(field):
                            if not value:
                                return []
                            try:
                                return [a.decode('utf-8') for a in literal_eval(value)]
                            except:
                                return [a.strip() for a in value.split(',')]
                        elif IDatetime.providedBy(field) and hasattr(value, 'day') and not hasattr(value, 'hour'):
                            value = datetime.datetime.combine(value, datetime.datetime.min.time())
                if name in ['expiration_date','effective_date', 'effective', 'expires'] and hasattr(value, 'day') and not hasattr(value, 'hour'):
                    value = datetime.datetime.combine(value, datetime.datetime.min.time())
                if isinstance(value, unicode) or name == 'id':
                    try:
                        value = str(value)
                    except:
                        pass
                return value
        return super(SQLDexterityItem, self).__getattribute__(name)
    
    def __setattr__(self, name, value):
        if name.startswith('_'):
            return super(SQLDexterityItem, self).__setattr__(name, value)
        connection = queryUtility(ISQLConnectionsUtility, name=self.portal_type, default=None)
        if connection and name in connection.fieldnames.keys():
            sql_column = connection.fieldnames[name]
            sql_item = self.getRawSQLItem()
#            if sql_item and sql_column:
#                return setattr(sql_item, sql_column, value)
            return
        return super(SQLDexterityItem, self).__setattr__(name, value)

    @security.protected(permissions.ModifyPortalContent)
    def setModificationDate(self, modification_date=None):
        """ Set the date when the resource was last modified.

        When called without an argument, sets the date to now.
        """
        connection = self.getConnection()
        if not 'modification_date' in connection.fieldnames.keys():
            return super(SQLDexterityItem, self).setModificationDate(modification_date)
        if modification_date is None:
            self.modification_date = datetime.datetime.now()
        else:
            self.modification_date = modification_date

    @security.protected(permissions.ModifyPortalContent)
    def setEffectiveDate(self, effective_date):
        # Set Dublin Core Date element - date resource becomes effective.
        connection = self.getConnection()
        if not 'modification_date' in connection.fieldnames.keys() and not 'effective_date' in connection.fieldnames.keys():
            return super(SQLDexterityItem, self).setEffectiveDate(effective_date)
        self.effective_date = effective_date

    @security.protected(permissions.ModifyPortalContent)
    def setExpirationDate(self, expiration_date):
        # Set Dublin Core Date element - date resource expires.
        connection = self.getConnection()
        if not 'expiration_date' in connection.fieldnames.keys():
            return super(SQLDexterityItem, self).setExpirationDate(expiration_date)
        self.expiration_date = expiration_date

    @security.protected(permissions.View)
    def modified(self):
        connection = self.getConnection()
        if not connection or not 'modification_date' in connection.fieldnames.keys():
            return super(SQLDexterityItem, self).modified()
        # Dublin Core Date element - date resource last modified.
        date = self.modification_date
        if date is None:
            # Upgrade.
            if self._p_mtime:
                date = self._p_mtime
            else:
                date = datetime.datetime.now()
            self.modification_date = date
        date = datify(date)
        return date

    def getPhysicalPath(self):
        """this needs implementation if the object doesnt exists for real in portal"""
        if not self.sql_virtual:
            return super(SQLDexterityItem, self).getPhysicalPath()
        portal_url = getToolByName(getSite(), 'portal_url')()
        fti = ISQLTypeSettings(getUtility(IDexterityFTI, name=self.portal_type))
        folder = None
        parent_path = None
        sql_folder_id = getattr(fti, 'sql_folder_id', None)
        if IRelationValue.providedBy(sql_folder_id):
            folder = sql_folder_id.to_object
            if folder:
                parent_path = folder.getPhysicalPath()
        elif hasattr(sql_folder_id, 'startswith') and sql_folder_id.startswith('/'):
            portal = getToolByName(getSite(), 'portal_url').getPortalObject()
            folder = portal.restrictedTraverse(sql_folder_id)
            if folder:
                parent_path = folder.getPhysicalPath()
        else:
			try:
				folder = uuidToObject(sql_folder_id)
				parent_path = folder.getPhysicalPath()
			except:
				pass
        if not parent_path:
            parent_path = ('', getSite().id, 'data-'+self.portal_type,)
        return parent_path+(str(self.id),)


@interface.implementer(IUUID)
@component.adapter(ISQLDexterityItem)
def attributeUUID(context):
    if not context.sql_virtual:
        return getattr(context, ATTRIBUTE_NAME, None)
    sql_id = getattr(context, 'sql_id', None)
    try:
        sql_id = str(unidecode(str(sql_id)))
    except:
        sql_id = str(unidecode(sql_id))
    return str(getattr(context, 'portal_type', ''))+'-'+sql_id


@implementer(IBrowserPublisher, ISQLItemPublisher)
class SQLItemPublisher(SimpleItem):

    def __init__(self, context, request):
        URL = request.get('URL')
        for a in [a for a in URL.split('/') if a.startswith('data-')]:
            self.fti_id = a.replace('data-','')
        self.fti = getUtility(IDexterityFTI, name=self.fti_id)
        self.name = 'data-'+self.fti_id
        self.id = 'data-'+self.fti_id
        self.Title = self.fti.Title()
        self.context = context
        self.request = request
        super(SQLItemPublisher, self).__init__(context, request)

    def getConnection(self):
        connection = queryUtility(ISQLConnectionsUtility, name=self.fti_id, default=None)
        if connection == None and self.fti_id:
            fti = queryUtility(IDexterityFTI, name=self.fti_id, default=None)
            if not fti:
                return None
            updateConnectionsForFti(fti)
            connection = queryUtility(ISQLConnectionsUtility, name=self.fti_id, default=None)
        return connection

    def getSQLItemByName(self, name):
        if name[0] in '-+':
            return None
        connection = self.getConnection()
        catalog = getToolByName(getSite(), 'portal_catalog')
        path = '/'.join(self.context.getPhysicalPath())
        results = catalog.unrestrictedSearchResults(portal_type=self.fti_id, id=name, path={'query':path})
        if results:
            if not results[0].sql_virtual:
                return results[0].getObject()
            sql_id = results[0].sql_id
        else:
            sql_id = name
        sql_id_column = self.fti.sql_id_column
        factory_utility = queryUtility(IFactory, name=self.fti.factory)
        params = {}
        params[sql_id_column] = sql_id
        sql_items = connection.query(**params)
        if sql_items:
            sql_item = sql_items[0]
            sql_item_id = getattr(sql_item, sql_id_column, False)
            item = factory_utility(sql_id=sql_item_id, sql_item=sql_item, sql_virtual=True)
            item.sql_virtual = True
            return item.__of__(self)
        return None

    def publishTraverse(self, request, name):
        item = self.getSQLItemByName(name)
        if item:
            return item
        return super(SQLItemPublisher, self).publishTraverse(request, name)

    def browserDefault(self, request):
        """Show the 'edit' view by default.

        If we aren't traversing to a schema beneath the types configlet,
        we actually want to see the TypesListingPage.
        """
        return self, ('@@data',)
    
    def restrictedTraverse(self, name):
        if name.startswith('@@') or name.startswith('++') or name.startswith('portal_') or name == 'main_template':
            return super(SQLItemPublisher, self).restrictedTraverse(name)
        item = self.getSQLItemByName(name)
        if item:
            return item
        return super(SQLItemPublisher, self).restrictedTraverse(name)


@adapter(ISQLTraverser, IBrowserRequest)
class SQLDexterityPublishTraverse(DexterityPublishTraverse):
    """Publisher for an item in the site to act like a folder for virtual sql content"""

    def __init__(self, context, request):
        super(SQLDexterityPublishTraverse, self).__init__(context, request)
        annotations = IAnnotations(context)
        self.fti_id = annotations.get('collective.behavior.sql.sql_type')
        if self.fti_id:
            self.fti = getUtility(IDexterityFTI, name=self.fti_id)
            name = getattr(ISQLTypeSettings(self.fti), 'sql_folder_id', self.fti_id)
            if name and IRelationValue.providedBy(name):
                obj = name.to_object
                if obj:
                    name = obj.getId()
                else:
                    name = self.fti_id
                
            elif name and name.startswith('/'):
                portal = getToolByName(getSite(), 'portal_url').getPortalObject()
                obj = portal.restrictedTraverse(name)
                if obj:
                    name = obj.getId()
                else:
                    name = self.fti_id
            elif not name:
                name = self.fti_id
            self.name = name
            self.Title = self.fti.Title()


    def publishTraverse(self, request, name):
        if not self.fti_id:
            return super(SQLDexterityPublishTraverse, self).publishTraverse(request, name)
        connection = queryUtility(ISQLConnectionsUtility, name=self.fti_id, default=None)
        if connection == None and self.portal_type:
            fti = queryUtility(IDexterityFTI, name=self.fti_id, default=None)
            if not fti:
                return None
            updateConnectionsForFti(self.fti)
            connection = getUtility(ISQLConnectionsUtility, name=self.fti_id)
        name = name.split('/')[0]
        name = name.split('++')[0]
        name = name.split('@@')[0]
        sql_id_column = self.fti.sql_id_column
        factory_utility = queryUtility(IFactory, name=self.fti.factory)
        catalog = getToolByName(getSite(), 'portal_catalog')
        results = catalog.unrestrictedSearchResults(portal_type=self.fti_id, id=name)
        if results:
            sql_id = results[0].sql_id
        else:
            sql_id = name
        try:
            sql_items = connection.query(id=sql_id)
        except:
            sql_items = []
        if sql_items:
            sql_item = sql_items[0]
            sql_item_id = getattr(sql_item, sql_id_column, False)
            item = factory_utility(sql_id=sql_item_id)
            item.sql_virtual = True
            return item.__of__(self.context)
        return super(SQLDexterityPublishTraverse, self).publishTraverse(request, name)


def unique_collection(base, local_cls, referred_cls, constraint):
    #there can be more that one relation between local_cls and referred_cls
    return referred_cls.__name__.lower()+'_'+constraint.table.name.lower() + "_collection"


def _gen_relationship(base, direction, return_fn,
                                attrname, local_cls, referred_cls, **kw):
    kw['lazy'] = 'subquery'
    return generate_relationship(base, direction, return_fn,
                                 attrname, local_cls, referred_cls, **kw)


@implementer(ISQLBaseConnectionUtility)
class SQLBaseConnectionUtility(object):
    
    # all theses values are set on the first time DexterityFTI is adapted to ISQLDexterityFTI
    # in a particular named utility with name = id of DexterityFTI

    @property
    def conn(self):
        return self.d_base.metadata.bind.contextual_connect(close_with_result=True)
    
    @property
    def session(self):
        return self._scoped_session()

    @property
    def insp(self):
        return self._insp

    def setupConnection(self):
        LOG.info('setupConnection:'+self.sql_url)
        if self._scoped_session:
            self._scoped_session.remove()
        try:
            engine = create_engine(self.sql_url, encoding='utf8', echo=False, pool_recycle=1)
        except:
            exc_type, exc_value, exc_traceback = sys.exc_info()
            lines = traceback.format_exception(exc_type, exc_value, exc_traceback)
            LOG.error(''.join('!! ' + line for line in lines))
            return
        self._insp = reflection.Inspector.from_engine(engine)
        self.d_base = declarative_base(bind=engine)
        a_base = automap_base(bind=engine)
        try:
            a_base.metadata.reflect(views=True)
            self.name = unicode(self.sql_url)
        except:
            LOG.info('Unable to reflect the whole DB!')
            exc_type, exc_value, exc_traceback = sys.exc_info()
            lines = traceback.format_exception(exc_type, exc_value, exc_traceback)
            for line in lines:
                LOG.info(line)
            a_base.metadata.reflect(views=True, only=[self.sql_table])
            self.restricted = True
            self.name = unicode(self.sql_url+'+'+self.sql_table)
        a_base.prepare(a_base.metadata.bind, name_for_collection_relationship=unique_collection, generate_relationship=_gen_relationship)
        self.a_base = a_base
        self._scoped_session = scoped_session(sessionmaker(bind=self.a_base.metadata.bind, extension=ZopeTransactionExtension(keep_session=True), autocommit=True, expire_on_commit=False))

    def __init__(self, fti=None):
        if not fti or not fti.sql_connection:
            return
        self.sql_connection = fti.sql_connection
        self.sql_url = fti.sql_url
        self.sql_table = fti.sql_table
        self.engine = None
        self.d_base = None # declarative base
        self.a_base = None # automatic base
        self._scoped_session = None
        self._session = None
        self._insp = None
        self._query = None
        self.restricted = False
        self.name = None
        self.setupConnection()


@implementer(ISQLConnectionsUtility)
class SQLConnectionsUtility(object):

    connection_name = False
    sql_table = None
    sql_id_column = None # id of the column that gives its id to the content
    factory = None # Factory name
    fieldnames = {} # dict of fields name : sql_column for the current schema type

    def __init__(self, fti=None):
        if not fti:
            return
        sql_connection = queryUtility(ISQLBaseConnectionUtility, name=fti.sql_url, default=None)
        if sql_connection:
            self.connection_name = sql_connection.name
        else:
            sql_connection = queryUtility(ISQLBaseConnectionUtility, name=fti.sql_table, default=None)
        if sql_connection:
            self.connection_name = sql_connection.name
        else:
            processor = SQLBaseConnectionUtility(fti)
            connection_name = processor.name
            LOG.info('Base connection utility registered as '+connection_name)
            gsm = getGlobalSiteManager()
            gsm.registerUtility(processor, ISQLBaseConnectionUtility, name=connection_name)
            self.connection_name = connection_name
        self.sql_table = fti.sql_table
        self.factory = fti.context.factory
        self.sql_id_column = getattr(fti, 'sql_id_column', None) and getattr(fti, 'sql_id_column', None) or 'id'
        fieldnames = {}
        for field_name, field in schema.getFieldsInOrder( fti.context.lookupSchema() ):
            if getattr(field, 'sql_column', None):
                sql_column = getattr(field, 'sql_column', None)
                fieldnames[field_name] = sql_column
        for line in getattr(fti, 'sql_fields_columns', []):
            fieldnames[line.split(':')[0]] = line.split(':')[1]
        self.fieldnames = fieldnames
    
    @property
    def conn(self):
        return getUtility(ISQLBaseConnectionUtility, name=self.connection_name).conn
    
    @property
    def session(self):
        return getUtility(ISQLBaseConnectionUtility, name=self.connection_name).session

    @property
    def insp(self):
        return getUtility(ISQLBaseConnectionUtility, name=self.connection_name).insp

    def reinit(self):
        baseconn = getUtility(ISQLBaseConnectionUtility, name=self.connection_name)
        baseconn.setupConnection()
        
    @property
    def tableClass(self):
        connection = getUtility(ISQLBaseConnectionUtility, name=self.connection_name)
        table = getattr(connection.a_base.classes, self.sql_table, None)
        if not table:
            table = connection.a_base.metadata.tables.get(self.sql_table)
        return table
    
    def query(self, id=None, **kwargs):
        if id != None:
            try:
                id = int(id)
            except:
                pass
            kwargs[self.sql_id_column] = id
        tableClass = self.tableClass
        if not tableClass:
            return []
        items = []
        try:
            query = self.session.query(tableClass)
            items = query.filter_by(**kwargs).all()
        except:
            LOG.info('orm_exc.StatementError')
            connection = getUtility(ISQLBaseConnectionUtility, name=self.connection_name)
            connection.setupConnection()
            query = self.session.query(tableClass)
            items = query.filter_by(**kwargs).all()
        return items

    def add(self, **kwargs):
        tableClass = self.tableClass
        if not tableClass:
            raise ValueError('No table class defined')
        item = tableClass(**kwargs)
        self.session.add(item)

    def getVirtualItem(self, name, context=None):
        sql_items = self.query(id=name)
        if sql_items:
            sql_item = sql_items[0]
            sql_item_id = getattr(sql_item, self.sql_id_column, False)
            factory_utility = queryUtility(IFactory, name=self.factory)
            item = factory_utility(sql_id=sql_item_id, sql_item=sql_item, sql_virtual=True)
            item.sql_virtual = True
            if context != None:
                return item.__of__(context)
            return item.__of__(self)
        return None


def registerPublisherForFTI(fti):
    # This registers a publisher that will allow to traverse to each sql item
    if not getattr(fti, 'sql_table', None):
        return
    sql_folder_id = getattr(fti, 'sql_folder_id', fti.id)
    has_folder = False
    if sql_folder_id:
		if IRelationValue.providedBy(sql_folder_id):
			obj = sql_folder_id.to_object
			if obj:
				has_folder = True
				name = obj.getId()
			else:
				name = fti.context.getId()
		elif sql_folder_id.startswith('/'):
			portal = getToolByName(getSite(), "portal_url").getPortalObject()
			try:
				folder = portal.restrictedTraverse(name)
				has_folder = True
			except:
				pass
		else:
			try:
				folder = uuidToObject(sql_folder_id)
				has_folder = True
			except:
				pass
    else:
        name = fti.context.getId()
    if not has_folder:
        view = queryMultiAdapter((None, ICollectiveBehaviorSQLLayer), IBrowserView, name='data-'+name, default=None)
        if not view:
			publisher = SQLItemPublisher
			provideAdapter(
				factory=publisher,
				adapts=(None, ICollectiveBehaviorSQLLayer),
				provides=IBrowserView,
				name='data-'+name)

			LOG.info('Publisher registered for data-'+name)

def registerConnectionUtilityForFTI(fti):
    # This registers an utility that will handle connections and sessions for each defined SQL DX types.
    if not ISQLTypeSettings.providedBy(fti):
        fti = ISQLTypeSettings(fti)
    utility = queryUtility(ISQLConnectionsUtility, name=fti.id, default=None)
    if utility != None:
        return utility
    if not getattr(fti, 'sql_table', None):
        return
    processor = SQLConnectionsUtility(fti)
    gsm = getGlobalSiteManager()
    gsm.registerUtility(processor, ISQLConnectionsUtility, name=fti.id)
    LOG.info('SQL Connection utility registered for '+fti.id)
    return getUtility(ISQLConnectionsUtility, name=fti.id)

def initConnectionForFTI(fti):
    if not ISQLTypeSettings.providedBy(fti):
        fti = ISQLTypeSettings(fti)
    registerPublisherForFTI(fti)
    registerConnectionUtilityForFTI(fti)

def initConnections(site, event):
    # this is called on first Plone traverse
    portal_quickinstaller = getToolByName(site, 'portal_quickinstaller')
    if portal_quickinstaller.isProductInstalled('collective.behavior.sql'):
        if not getAllUtilitiesRegisteredFor(ISQLConnectionsUtility):
            ftis = [a for a in getAllUtilitiesRegisteredFor(IDexterityFTI) if 'collective.behavior.sql.behavior.behaviors.ISQLContent' in a.behaviors and getattr(a, 'sql_table', None)]
            if ftis:
                for fti in ftis:
                    if not ISQLTypeSettings.providedBy(fti):
                        fti = ISQLTypeSettings(fti)
                    try:
                        initConnectionForFTI(fti)
                    except:
                        LOG.error('Unable to init connection for %s' % (fti.id))
                        gsm = getGlobalSiteManager()
                        gsm.registerUtility(SQLConnectionsUtility(), ISQLConnectionsUtility)
            else:
                gsm = getGlobalSiteManager()
                gsm.registerUtility(SQLConnectionsUtility(), ISQLConnectionsUtility)


def updateConnectionsForFti(fti):
    # find the FTI and model
    if not ISQLTypeSettings.providedBy(fti):
        fti = ISQLTypeSettings(fti)
    connection = queryUtility(ISQLConnectionsUtility, name=fti.id, default=None)
    if not connection:
        connection = registerConnectionUtilityForFTI(fti)
    if not getattr(connection, 'name', None):
        return
    registerPublisherForFTI(fti)
    sql_id_column = getattr(fti, 'sql_id_column', 'id')
#    fieldnames = {'id':sql_id_column}
    fieldnames = {}
    for field_name, field in schema.getFieldsInOrder( fti.context.lookupSchema() ):
        if getattr(field, 'sql_column', None):
            sql_column = getattr(field, 'sql_column', None)
            fieldnames[field_name] = sql_column
    for line in getattr(fti, 'sql_fields_columns', []):
        fieldnames[line.split(':')[0]] = line.split(':')[1]
    connection.fieldnames = fieldnames
    sqlfti = fti.updateCatalogItems()


def updateConnections(schema_context, event=None):
    LOG.info('updateConnections')
    updateConnectionsForFti(schema_context.fti)


def reindexOnModify(content, event=None):
    if event.object is not content:
        return
    uid = '/'.join(content.getPhysicalPath())
    catalog = getToolByName(getSite(), "portal_catalog")
    if list(catalog.unrestrictedSearchResults(path=uid)):
        catalog.uncatalog_object(uid)
    catalog.catalog_object(content)

