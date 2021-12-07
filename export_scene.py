
#
# This script is licensed as public domain.
#

from .utils import PathType, GetFilepath, CheckFilepath, \
                   FloatToString, Vector3ToString, Vector4ToString, \
                   WriteXmlFile

from xml.etree import ElementTree
from mathutils import Vector, Quaternion, Matrix
import bpy
import os
import logging
import math
import copy

log = logging.getLogger("ExportLogger")


#-------
# Utils
#-------

# Get the object quaternion rotation, convert if it uses other rotation modes
def GetQuatenion(obj):
    # Quaternion mode
    if obj.rotation_mode == 'QUATERNION':
        return obj.rotation_quaternion
    # Axis Angle mode
    if obj.rotation_mode == 'AXIS_ANGLE':
        rot = obj.rotation_axis_angle
        return Quaternion(Vector((rot[1], rot[2], rot[3])), rot[0])
    # Euler mode
    return obj.rotation_euler.to_quaternion()


#-------------------------
# Scene and nodes classes
#-------------------------

# Options for scene and nodes export
class SOptions:
    def __init__(self):
        self.doObjectsPrefab = False
        self.doCollectivePrefab = False
        self.doFullScene = False
        self.onlySelected = False
        self.physics = False
        self.collisionShape = None
        self.trasfObjects = False
        self.globalOrigin = False
        self.orientation = Quaternion((1.0, 0.0, 0.0, 0.0))

class UrhoSceneMaterial:
    def __init__(self):
        # Material name
        self.name = None
        # List\Tuple of textures
        self.texturesList = None

    def LoadMaterial(self, uExportData, uGeometry):
        self.name = uGeometry.uMaterialName
        for uMaterial in uExportData.materials:
            if uMaterial.name == self.name:
                self.texturesList = uMaterial.getTextures()
                break

class UrhoSceneModel:
    def __init__(self):
        # Model name
        self.name = None
        # Blender object name
        self.blenderName = None
        # Parent Blender object name
        self.parentBlenderName = None
        # Model type
        self.type = None
        # List of UrhoSceneMaterial
        self.materialsList = []
        # Model bounding box
        self.boundingBox = None
        # Model position
        self.position = Vector()
        # Model rotation
        self.rotation = Quaternion((1.0, 0.0, 0.0, 0.0))
        # Model scale
        self.scale = Vector((1.0, 1.0, 1.0))

    def LoadModel(self, uExportData, uModel, blenderObjectName, sOptions):
        self.name = uModel.name

        self.blenderName = blenderObjectName
        if self.blenderName:
            object = bpy.data.objects[self.blenderName]

            # Get the local matrix (relative to parent)
            objMatrix = object.matrix_local
            # Reorient (normally only root objects need to be re-oriented but 
            # here we need to undo the previous rotation done by DecomposeMesh)
            if sOptions.orientation:
                om = sOptions.orientation.to_matrix().to_4x4()
                objMatrix = om @ objMatrix @ om.inverted()

            # Get pos/rot/scale
            pos = objMatrix.to_translation()
            rot = objMatrix.to_quaternion()
            scale = objMatrix.to_scale()

            # Convert pos/rot/scale
            self.position = Vector((pos.x, pos.z, pos.y))
            self.rotation = Quaternion((rot.w, -rot.x, -rot.z, -rot.y))
            self.scale = Vector((scale.x, scale.z, scale.y))

            # Get parent object
            parentObject = object.parent
            if parentObject and parentObject.type == 'MESH':
                self.parentBlenderName = parentObject.name

        if uModel.type != 'MESH':
            self.type = uModel.type
        elif len(uModel.bones) > 0 or len(uModel.morphs) > 0:
            self.type = "AnimatedModel"
        else:
            self.type = "StaticModel"

        for uGeometry in uModel.geometries:
            uSceneMaterial = UrhoSceneMaterial()
            uSceneMaterial.LoadMaterial(uExportData, uGeometry)
            self.materialsList.append(uSceneMaterial)

        self.boundingBox = uModel.boundingBox

class UrhoScene:
    def __init__(self, blenderScene):
        # Blender scene name
        self.blenderSceneName = blenderScene.name
        # List of UrhoSceneModel
        self.modelsList = []
        # List of all files
        self.files = {}

    def LoadScene(self, uExportData, blenderObjectName, sOptions):
        for uModel in uExportData.models:
            uSceneModel = UrhoSceneModel()
            uSceneModel.LoadModel(uExportData, uModel, blenderObjectName, sOptions)
            self.modelsList.append(uSceneModel)

    def AddFile(self, pathType, name, fileUrhoPath):
        # Note: name must be unique in its type
        if not name:
            log.critical("Name null type:{:s} path:{:s}".format(pathType, fileUrhoPath) )
            return False
        if name in self.files:
            log.critical("Already added type:{:s} name:{:s}".format(pathType, name) )
            return False
        self.files[pathType+name] = fileUrhoPath
        return True

    def FindFile(self, pathType, name):
        if name is None:
            return ""
        try:
            return self.files[pathType+name]
        except KeyError:
            return ""


#------------
# Scene sort
#------------

# Hierarchical sorting (based on a post by Hyperboreus at SO)
class Node:
    def __init__(self, name):
        self.name = name
        self.children = []
        self.parent = None

    def to_list(self):
        names = [self.name]
        for child in self.children:
            names.extend(child.to_list())
        return names
            
class Tree:
    def __init__(self):
        self.nodes = {}

    def push(self, item):
        name, parent = item
        if name not in self.nodes:
            self.nodes[name] = Node(name)
        if parent:
            if parent not in self.nodes:
                self.nodes[parent] = Node(parent)
            if parent != name:
                self.nodes[name].parent = self.nodes[parent]
                self.nodes[parent].children.append(self.nodes[name])

    def to_list(self):
        names = []
        for node in self.nodes.values():
            if not node.parent:
                names.extend(node.to_list())
        return names

# Sort scene models by parent-child relation
def SceneModelsSort(scene):
    names_tree = Tree()
    for model in scene.modelsList:
        ##names_tree.push((model.objectName, model.parentBlenderName))
        names_tree.push((model.name, model.parentBlenderName))
    # Rearrange the model list in the new order
    orderedModelsList = []
    for name in names_tree.to_list():
        for model in scene.modelsList:
            ##if model.objectName == name:
            if model.name == name:
                orderedModelsList.append(model)
                # No need to reverse the list, we break straightway
                scene.modelsList.remove(model)
                break
    scene.modelsList = orderedModelsList


#--------------
# XML elements
#--------------

# Create an XML element using 'tag' as name and the dictionary  'values'
# as attributes, if 'parent' is None a root element is created.
def XmlAddElement(parent, tag, ids=None, values=None):
    if parent is not None:
        element = ElementTree.SubElement(parent, tag)
    else:
        element = ElementTree.Element(tag)
    if ids is not None:
        element.set("id", str(ids[tag]))
        ids[tag] += 1
    if values is not None:
        for name, value in values.items():
            element.set(name, str(value))
    return element

# Adds to parent an XML element with name "component" and attributes 
# "type" and "id", the value of "id" is taken from the 'ids' dictionary.
def XmlAddComponent(parent=None, type=None, ids=None):
    if parent is not None:
        element = ElementTree.SubElement(parent, "component")
    else:
        element = ElementTree.Element("component")
    if type is not None:
        element.set("type", str(type))
    if ids is not None:
        element.set("id", str(ids["component"]))
        ids["component"] += 1
    return element

# Adds to parent an XML element with name "attribute" and attributes 
# "name" and "value".
def XmlAddAttribute(parent=None, name=None, value=None):
    if parent is not None:
        element = ElementTree.SubElement(parent, "attribute")
    else:
        element = ElementTree.Element("attribute")
    if name is not None:
        element.set("name", str(name))
    if value is not None:
        element.set("value", str(value))
    return element

# Removes from 'node' all the child nodes whose attribute 'name' is not 
# in the list 'values'.
def XmlNodeFilter(node, name, values):
    for child in list(node):
        if child.tag != "node":
            continue
        value = child.get(name, None)
        if value in values:
            XmlNodeFilter(child, name, values)
        else:
            node.remove(child)

# Renumber the attribute "id" of 'node' and all its children, each different
# element tag has a different numbering starting from 1. Use the dictionary
# 'ids' ("tag":number) to specify a custom start.
def XmlIdSet(node, ids = None):
    if ids is None: # dict as default arg is static
        ids = {}
    tag = node.tag
    if tag not in ids:
        ids[tag] = 1
    if node.get("id", False):
        node.set("id", str(ids[tag]))
        ids[tag] += 1
    for child in list(node):
        XmlIdSet(child, ids)

#------------------------
# Export materials
#------------------------

"""
def UrhoWriteMaterial(uScene, uMaterial, filepath, fOptions):

    material = XmlAddElement(None, "material")

    # Technique
    techniquFile = GetFilepath(PathType.TECHNIQUES, uMaterial.techniqueName, fOptions)
    XmlAddElement(material, "technique",
        values={"name": techniquFile[1]} )

    # Textures
    for texKey, texName in uMaterial.texturesNames.items():
        if texName:
            XmlAddElement(material, "texture",
                values={"unit": texKey, "name": uScene.FindFile(PathType.TEXTURES, texName)} )

    # PS defines
    if uMaterial.psdefines != "":
        XmlAddElement(material, "shader",
            values={"psdefines": uMaterial.psdefines.lstrip()} )

    # VS defines
    if uMaterial.vsdefines != "":
        XmlAddElement(material, "shader",
            values={"vsdefines": uMaterial.vsdefines.lstrip()} )

    # Parameters
    if uMaterial.diffuseColor:
        XmlAddElement(material, "parameter",
            values={"name": "MatDiffColor", "value": Vector4ToString(uMaterial.diffuseColor)} )

    if uMaterial.specularColor:
        XmlAddElement(material, "parameter",
            values={"name": "MatSpecColor", "value": Vector4ToString(uMaterial.specularColor)} )

    if uMaterial.emissiveColor:
        XmlAddElement(material, "parameter",
            values={"name": "MatEmissiveColor", "value": Vector3ToString(uMaterial.emissiveColor)} )

    if uMaterial.twoSided:
        XmlAddElement(material, "cull",
            values={"value": "none"} )
        XmlAddElement(material, "shadowcull",
            values={"value": "none"} )

    WriteXmlFile(material, filepath, fOptions)
"""


def UrhoWriteMaterialsList(uScene, uModel, filepath):

    # Search for the model in the UrhoScene
    for uSceneModel in uScene.modelsList:
        if uSceneModel.name == uModel.name:
            break
    else:
        return

    # Get the model materials and their corresponding file paths
    content = ""
    for uSceneMaterial in uSceneModel.materialsList:
        file = uScene.FindFile(PathType.MATERIALS, uSceneMaterial.name)
        # If the file is missing add a placeholder to preserve the order
        if not file:
            file = "null"
        content += file + "\n"

    try:
        file = open(filepath, "w")
    except Exception as e:
        log.error("Cannot open file {:s} {:s}".format(filepath, e))
        return
    file.write(content)
    file.close()


#------------------------
# Export scene and nodes
#------------------------

def NELExportBone(armature, bone, XMLparent, ids, extractPosition, needBones):
    node = XmlAddElement(XMLparent, "node", ids=ids)
    XmlAddAttribute(node, name="Is Enabled", value="true") #extra
    XmlAddAttribute(node, name="Name", value=bone.name)
    XmlAddAttribute(node, name="Tags", value='BONE') #extra
    
    extractPosition(bone,node)
    
    if bone.name in needBones:
        for o in needBones[bone.name]:
            NELExportObject(o,node,ids,extractPosition)
        
    for b in bone.children:
        NELExportBone(armature,b,node,ids,extractPosition,needBones)

def NELExportObject(object, XMLparent, ids, extractPosition):
    
    if object.parent and object.parent.type == 'ARMATURE' and object.parent_type != 'BONE':
        node = XMLparent
        XmlAddAttribute(node, name="Tags", value='NEED TO CONFIRM POSITION IS THE SAME') #extra
    else:
        node = XmlAddElement(XMLparent, "node", ids=ids)
            
        XmlAddAttribute(node, name="Is Enabled", value="true") #extra
        XmlAddAttribute(node, name="Name", value=object.name)
        XmlAddAttribute(node, name="Tags", value=str(object.type)) #extra
        #XmlAddAttribute(node, name="Variables") #extra
    
        extractPosition(object,node)
        
    
    if object.type == 'MESH':
        modelFile = f"Models/{object.name}.mdl"
        materials = ';'.join(f"Materials/{m.name}.xml" for m in object.data.materials)
        
        comp = XmlAddComponent(node, type='AnimatedModel', ids=ids)
        XmlAddAttribute(comp, name="Model", value="Model;" + modelFile)
        XmlAddAttribute(comp, name="Material", value="Material" + materials)
    elif object.type == 'LIGHT':
        comp = XmlAddComponent(node, type="Light", ids=ids)
        ltype = object.data.type
        if ltype == 'SUN':
            ltype = 'Directional'
        elif ltype == 'SPOT':
            ltype = 'Spot'
        # Can't do area lights in Urho, so fall back to point
        else:
            ltype = 'Point'
        XmlAddAttribute(comp, name="Light Type", value=ltype)
        color = object.data.color
        XmlAddAttribute(comp, name="Color", value=' '.join(map(str,color)))
        
    elif object.type == 'CAMERA':
        comp = XmlAddComponent(node, type="Camera", ids=ids)
    
    from collections import defaultdict
    needBones = defaultdict(list)
    for o in object.children:
        if o.parent_type != 'BONE':
            NELExportObject(o,node,ids,extractPosition)
        else:
            needBones[o.parent_bone].append(o)
    if needBones:
        if object.type != 'ARMATURE':
            log.warning("How does the child have a bone parent that is not an armature!?!")
        else:
            arma = object.data
            rootBones = []
            for b in arma.bones:
                if b.parent is None:
                    NELExportBone(object,b,node,ids,extractPosition,needBones)
            
            
            

def NELExportScene(context, uScene, sOptions, fOptions):
    
    def extractPosition(object,node):
        if type(object) == bpy.types.Bone:
            bone = object
            tOptions = sOptions
            
            # From decompose.py
            # 'bone.matrix_local' is referred to the armature, we need
            # the transformation between the current bone and its parent.
            boneMatrix = bone.matrix_local.copy()
            
            # Here 'bone.matrix_local' is in object(armature) space, so we have to
            # calculate the bone transformation in parent bone space
            if bone.parent:
                boneMatrix = bone.parent.matrix_local.inverted() @ boneMatrix
            else:
                #boneMatrix = originMatrix @ boneMatrix
                if tOptions.orientation:
                    boneMatrix = tOptions.orientation.to_matrix().to_4x4() @ boneMatrix
                # Normally we don't have to worry that Blender is Z up and we want
                # Y up because we use relative transformations between bones. However
                # the parent bone is relative to the armature so we need to convert
                # Z up to Y up by rotating its matrix by -90° on X
                boneMatrix = Matrix.Rotation(math.radians(-90.0), 4, 'X' ) @ boneMatrix

            if tOptions.scale != 1.0:
                boneMatrix.translation *= tOptions.scale

            # Extract position and rotation relative to parent in parent space        
            t = boneMatrix.to_translation()
            q = boneMatrix.to_quaternion()
            s = boneMatrix.to_scale()
                    
            # Convert position and rotation to left hand:
            tl = Vector((t.x, t.y, -t.z))
            ql = Quaternion((q.w, -q.x, -q.y, q.z))
            sl = Vector((s.x, s.y, s.z))
            
            # Now we need the bone matrix relative to the armature. 'matrix_local' is
            # what we are looking for, but it needs to be converted:
            # 1) rotate of -90° on X axis:
            # - swap column 1 with column 2
            # - negate column 1
            # 2) convert bone transformation in object space to left hand:        
            # - swap row 1 with row 2
            # - swap column 1 with column 2
            # So putting them together:
            # - swap row 1 with row 2
            # - negate column 2
            ml = bone.matrix_local.copy()
            if tOptions.orientation:
                ml = tOptions.orientation.to_matrix().to_4x4() @ ml
            if tOptions.scale != 1.0:
                ml.translation *= tOptions.scale
            (ml[1][:], ml[2][:]) = (ml[2][:], ml[1][:])
            ml[0][2] = -ml[0][2]
            ml[1][2] = -ml[1][2]
            ml[2][2] = -ml[2][2]

            # Create a new bone
            position = tl
            rotation = ql
            scale = sl
        else:
            if not sOptions.trasfObjects:
                return
            # Get the local matrix (relative to parent)
            objMatrix = object.matrix_local
            
            orientation = sOptions.orientation
            onBone = False
            # Blender's Parent to Bone feature parents it to the point of the bone, while urho only uses the socket (other) end.
            # As such, we have to offset the matrix by the bone length or it will be incorrect.
            if object.parent and object.parent_type == 'BONE':
                onBone = True
                bone = object.parent.data.bones[object.parent_bone]
                objMatrix = Matrix(objMatrix) # Copy so we don't modify the object
                objMatrix[1][3] += bone.length
                backup = objMatrix.copy()
                # We also need to correct the orientation
                from math import radians,pi
                orientations = {
                
                    'X_PLUS': Quaternion((0.0,0.0,1.0), radians(90.0)),
                    'X_MINUS': Quaternion((0.0,0.0,1.0), radians(-90.0)),
                    'Y_PLUS': Quaternion((0.0,0.0,1.0), radians(0.0)),
                    'Y_MINUS': Quaternion((0.0,0.0,1.0), radians(180.0)),
                    'Z_PLUS': Quaternion((1.0,0.0,0.0), radians(-90.0)) @ Quaternion((0.0,0.0,1.0), radians(180.0)), # Gives correct translation but incorrect rotation
                    'Z_MINUS': Quaternion((1.0,0.0,0.0), radians(90.0)) @ Quaternion((0.0,0.0,1.0), radians(180.0))    
                }
                for obef in [True,False]:
                    break
                    for bot in [True,False]:
                        for bef in [True,False]:
                            for l,o in orientations.items():
                                om = o.to_matrix().to_4x4()
                                m = objMatrix.copy()
                                if obef:
                                    m = om @ m @ om.inverted()
                                if bot:
                                    if bef:
                                        m = Matrix.Rotation(math.radians(-90.0), 4, 'X' ) @ m @ Matrix.Rotation(math.radians(90.0), 4, 'X' )
                                    else:
                                        m = Matrix.Rotation(math.radians(90.0), 4, 'X' ) @ m @ Matrix.Rotation(math.radians(-90.0), 4, 'X' )
                                elif bef:
                                    m = Matrix.Rotation(math.radians(90.0), 4, 'X' ) @ m
                                else:
                                    m = m @ Matrix.Rotation(math.radians(90.0), 4, 'X' )
                                if not obef:
                                    m = om @ m @ om.inverted()

                                # Get pos/rot/scale
                                pos = m.to_translation()
                                rot = m.to_quaternion()
                                scale = m.to_scale()

                                # Convert pos/rot/scale
                                position = Vector((pos.x, pos.z, pos.y))
                                rotation = Quaternion((rot.w, -rot.x, -rot.z, -rot.y))
                                scale = Vector((scale.x, scale.z, scale.y))
                                XmlAddAttribute(node, name="LABEL", value=l+('(' if bef else ')'))
                                XmlAddAttribute(node, name="Position", value=Vector3ToString(position))
                                XmlAddAttribute(node, name="Rotation", value=Vector4ToString(rotation))
                
                #orientation = Quaternion((1.0,0.0,0.0), radians(90.0)) @ Quaternion((0.0,0.0,1.0), radians(180.0)) # Puts it behind
                orientation = Quaternion((1.0,0.0,0.0), radians(-90.0)) @ Quaternion((0.0,0.0,1.0), radians(180.0)) # Gives right translation but wrong orientation
                #orientation = Quaternion((1.0,0.0,0.0),0.0) 
            
            # Reorient (normally only root objects need to be re-oriented but 
            # here we need to undo the previous rotation done by DecomposeMesh)
            if onBone:
                M = Matrix.Rotation(pi,4,'Z') @ Matrix.Rotation(math.radians(-90.0), 4, 'X' )
                
                
                #log.warning(str(M.to_3x3()))
                #log.warning(str(M.to_3x3().inverted()))
                #log.warning(objMatrix)
                #log.warning(objMatrix @ M)
                #log.warning(Matrix.Rotation(pi,4,'Y') @ objMatrix@ Matrix.Rotation(math.radians(-90.0), 4, 'X' ))
                #log.warning(Matrix.Rotation(math.radians(-90.0), 4, 'X' ) @ objMatrix@ Matrix.Rotation(pi,4,'Y'))
                
                #objMatrix = objMatrix @ M # Working but X and Z translation are negated. Orientation is right, if the object is directly along the bone's axis.
                #objMatrix = objMatrix @ M
                
                # This is working for Left (X_MINUS) view. But not for Front.
                objMatrix = Matrix.Rotation(pi,4,'Y') @ objMatrix @ Matrix.Rotation(pi,4,'Y') @ Matrix.Rotation(math.radians(-90.0), 4, 'X' ) @ Matrix.Rotation(math.radians(90.0), 4, 'Y' )
                
                log.warning('Worked for X_MINUS')
                log.warning(orientation.to_matrix().to_4x4() @ Matrix.Rotation(pi,4,'Y') @ Matrix.Rotation(math.radians(-90.0), 4, 'X' ) @ Matrix.Rotation(math.radians(90.0), 4, 'Y' ))
                log.warning(Matrix.Rotation(pi,4,'Y') @ Matrix.Rotation(math.radians(-90.0), 4, 'X' ) @ Matrix.Rotation(math.radians(90.0), 4, 'Y' ) @ orientation.to_matrix().to_4x4().inverted())
                
                log.warning('Orientation for X_MINUS')
                log.warning(orientations['X_MINUS'].to_matrix().to_4x4())
                log.warning(orientations['X_MINUS'].to_matrix().to_4x4().inverted())
                
                log.warning('Proposed correct')
                xm = orientations['X_MINUS'].to_matrix().to_4x4()
                ori = (Quaternion((1.0,0.0,0.0), radians(-90.0)) @ Quaternion((0.0,0.0,1.0), radians(180.0))).to_matrix().to_4x4()
                log.warning(xm.inverted() @ ori @ 
                            Matrix.Rotation(pi,4,'Y') @ Matrix.Rotation(math.radians(-90.0), 4, 'X' ) @ Matrix.Rotation(math.radians(90.0), 4, 'Y' ))
                log.warning(Matrix.Rotation(pi,4,'Y') @ Matrix.Rotation(math.radians(-90.0), 4, 'X' ) @ Matrix.Rotation(math.radians(90.0), 4, 'Y' ) @ ori @ xm)
                
                #objMatrix = Matrix((( 0.0000, -1.0000, 0.0000, 0.0000),
                    #( 0.0000,  0.0000, 1.0000, 0.0000),
                    #(-1.0000, -0.0000, 0.0000, 0.0000),
                    #( 0.0000,  0.0000, 0.0000, 1.0000))) @ objMatrix
            
                
                # Compare with our proposed ideal case:
            
                """ Ops above (and below with the orientation) are 
                objMatrix = Matrix.Rotation(pi,4,'Y') @ objMatrix @ Matrix.Rotation(pi,4,'Y') @ Matrix.Rotation(math.radians(-90.0), 4, 'X' ) @ Matrix.Rotation(math.radians(90.0), 4, 'Y' )
                orientation = Quaternion((1.0,0.0,0.0), radians(-90.0)) @ Quaternion((0.0,0.0,1.0), radians(180.0))
                om = orientation.to_matrix().to_4x4()
                objMatrix = om @ objMatrix @ om.inverted()
                
                In other words
                
                X-90 Z+180 Y+180 _M_ Y+180 X-90 Y+90 (X-90 Z+180)^-1
                OR
                X-90 Z+180 Y+180 _M_ Y+180 X-90 Y+90 Z+180 X+90
                OR
                X-90 Z+180 Y+180
                """
                # We want to not fix orientation
                orientation = sOptions.orientation # = Quaternion((0.0,0.0,1.0), radians(-90.0)) for X_MINUS
                if orientation is None:
                    orientation = Quaternion((0,0,1),0)
                matrix = backup
                matrix = Matrix.Rotation(pi,4,'Y') @ matrix @ Matrix.Rotation(pi,4,'Y') @ Matrix.Rotation(math.radians(-90.0), 4, 'X' ) @ Matrix.Rotation(math.radians(90.0), 4, 'Y' )
                ori = (Quaternion((1.0,0.0,0.0), radians(-90.0)) @ Quaternion((0.0,0.0,1.0), radians(180.0))).to_matrix().to_4x4()
                matrix = ori @ matrix @ ori.inverted()
                
                xm = Quaternion((0.0,0.0,1.0), radians(-90.0)).to_matrix().to_4x4()
                matrix = xm.inverted() @ matrix @ xm
                # At end : 
                om = orientation.to_matrix().to_4x4()
                matrix = om @ matrix @ om.inverted()
                # For X_MINUS this is Z-90 _M_ Z+90
                
                log.warning('Check')
                log.warning(matrix)
                
                LEFT = xm.inverted() @ ori @ Matrix.Rotation(pi,4,'Y')
                RIGHT = Matrix.Rotation(pi,4,'Y') @ Matrix.Rotation(math.radians(-90.0), 4, 'X' ) @ Matrix.Rotation(math.radians(90.0), 4, 'Y' ) @ ori.inverted() @ xm
                log.warning('Check2')
                log.warning(om @ LEFT @ backup @ RIGHT @ om.inverted())
                log.warning(LEFT)
                log.warning(RIGHT)
                
                LEFT = Matrix(((0,0,1,0),(1,0,0,0),(0,1,0,0),(0,0,0,1)))
                RIGHT = Matrix.Identity(4)
                
                objMatrix = LEFT @ backup @ RIGHT
                
                om = orientation.to_matrix().to_4x4()
                #objMatrix = om @ objMatrix @ om.inverted()
                objMatrix = xm @ objMatrix @ om.inverted() # This line works for all but back, which has None orientation
                
                
                log.warning('Final')
                log.warning(objMatrix)
            
            elif orientation: # Try removing this point of variation from the bones
                om = orientation.to_matrix().to_4x4()
                objMatrix = om @ objMatrix @ om.inverted()
                #if onBone:
                    #log.warning('Final')
                    #log.warning(objMatrix)

            # Get pos/rot/scale
            pos = objMatrix.to_translation()
            rot = objMatrix.to_quaternion()
            scale = objMatrix.to_scale()

            # Convert pos/rot/scale
            position = Vector((pos.x, pos.z, pos.y))
            rotation = Quaternion((rot.w, -rot.x, -rot.z, -rot.y))
            scale = Vector((scale.x, scale.z, scale.y))
        
        XmlAddAttribute(node, name="Position", value=Vector3ToString(position))
        XmlAddAttribute(node, name="Rotation", value=Vector4ToString(rotation))
        XmlAddAttribute(node, name="Scale", value=Vector3ToString(scale))
        

    ids = {}
    ids["scene"] = 1
    ids["node"] = 1
    ids["component"] = 1
    
    rootNode = XmlAddElement(None, "node", ids=ids)
    XmlAddComponent(rootNode, type="Octree", ids=ids)
    XmlAddComponent(rootNode, type="DebugRenderer", ids=ids)
    XmlAddAttribute(rootNode, name="Is Enabled", value="true") #extra
    XmlAddAttribute(rootNode, name="Name", value=context.scene.name)
    #XmlAddAttribute(rootNode, name="Tags") #extra
    #XmlAddAttribute(rootNode, name="Variables") #extra
    
    for o in context.scene.objects:
        if o.parent is not None:
            continue # Only deal with the top level objects
        NELExportObject(o,rootNode,ids,extractPosition)


    XmlIdSet(rootNode)
    filepath = GetFilepath(PathType.OBJECTS, context.scene.name, fOptions)
    if CheckFilepath(filepath[0], fOptions):
        log.info( "Creating collective prefab {:s}".format(filepath[1]) )
        WriteXmlFile(rootNode, filepath[0], fOptions)

def UrhoExportScene(context, uScene, sOptions, fOptions):

    ids = {}
    ids["scene"] = 1
    ids["node"] = 1
    ids["component"] = 1

    # Root XML element
    root = XmlAddElement(None, "scene", ids=ids)
    XmlAddComponent(root, type="Octree", ids=ids)
    XmlAddComponent(root, type="DebugRenderer", ids=ids)
    comp = XmlAddComponent(root, type="Light", ids=ids)
    XmlAddAttribute(comp, name="Light Type", value="Directional")
    if sOptions.physics:
        XmlAddComponent(root, type="PhysicsWorld", ids=ids)

    # Root node
    rootNode = XmlAddElement(root, "node", ids=ids)
    XmlAddAttribute(rootNode, name="Is Enabled", value="true") #extra
    XmlAddAttribute(rootNode, name="Name", value=uScene.blenderSceneName)
    XmlAddAttribute(rootNode, name="Tags") #extra
    XmlAddAttribute(rootNode, name="Variables") #extra

    # Create physics stuff for the root node
    if sOptions.physics:
        comp = XmlAddComponent(rootNode, type="RigidBody", ids=ids)
        XmlAddAttribute(comp, name="Collision Layer", value="2")
        XmlAddAttribute(comp, name="Use Gravity", value="false")

        physicsModelFile = GetFilepath(PathType.MODELS, "Physics", fOptions)[1]
        comp = XmlAddComponent(rootNode, type="CollisionShape", ids=ids)
        XmlAddAttribute(comp, name="Shape Type", value="TriangleMesh")
        XmlAddAttribute(comp, name="Model", value="Model;" + physicsModelFile)

    if sOptions.trasfObjects and sOptions.globalOrigin:
        log.warning("To export objects transformations you should use Origin = Local")

    # Sort the models by parent-child relationship
    SceneModelsSort(uScene)

    # Blender object name to xml node collection
    xmlNodes = {}

    # Export each model object as a node
    for uSceneModel in uScene.modelsList:

        # Blender name is surely unique
        blenderName = uSceneModel.blenderName

        # Find the XML element of the model parent if it exists
        parent = rootNode
        if uSceneModel.type == "StaticModel":
            parentName = uSceneModel.parentBlenderName
            if parentName in xmlNodes:
                parent = xmlNodes[parentName]

        # Get model file relative path
        modelFile = uScene.FindFile(PathType.MODELS, uSceneModel.name)

        # Gather materials
        materials = ""
        for uSceneMaterial in uSceneModel.materialsList:
            file = uScene.FindFile(PathType.MATERIALS, uSceneMaterial.name)
            materials += ";" + file

        # Generate the node XML content
        node = XmlAddElement(parent, "node", ids=ids)
        xmlNodes[blenderName] = node
        XmlAddAttribute(node, name="Is Enabled", value="true") #extra
        XmlAddAttribute(node, name="Name", value=uSceneModel.name)
        XmlAddAttribute(node, name="Tags") #extra
        if sOptions.trasfObjects:
            XmlAddAttribute(node, name="Position", value=Vector3ToString(uSceneModel.position))
            XmlAddAttribute(node, name="Rotation", value=Vector4ToString(uSceneModel.rotation))
            XmlAddAttribute(node, name="Scale", value=Vector3ToString(uSceneModel.scale))
        XmlAddAttribute(node, name="Variables") #extra

        if uSceneModel.type == 'MESH':
            comp = XmlAddComponent(node, type=uSceneModel.type, ids=ids)
            XmlAddAttribute(comp, name="Model", value="Model;" + modelFile)
            XmlAddAttribute(comp, name="Material", value="Material" + materials)

        if sOptions.physics:
            # Use model's bounding box to compute CollisionShape's size and offset
            bbox = uSceneModel.boundingBox
            # Size
            shapeSize = Vector()
            if bbox.min and bbox.max:
                shapeSize.x = bbox.max[0] - bbox.min[0]
                shapeSize.y = bbox.max[1] - bbox.min[1]
                shapeSize.z = bbox.max[2] - bbox.min[2]
            # Offset
            shapeOffset = Vector()
            if bbox.max:
                shapeOffset.x = bbox.max[0] - shapeSize.x / 2
                shapeOffset.y = bbox.max[1] - shapeSize.y / 2
                shapeOffset.z = bbox.max[2] - shapeSize.z / 2

            comp = XmlAddComponent(node, type="RigidBody", ids=ids)
            XmlAddAttribute(comp, name="Collision Layer", value="2")
            XmlAddAttribute(comp, name="Use Gravity", value="false")

            comp = XmlAddComponent(node, type="CollisionShape", ids=ids)
            shapeType = sOptions.collisionShape
            XmlAddAttribute(comp, name="Shape Type", value=shapeType)
            if shapeType == "TriangleMesh":
                XmlAddAttribute(comp, name="Model", value="Model;" + modelFile)
            else:
                XmlAddAttribute(comp, name="Size", value=Vector3ToString(shapeSize))
                XmlAddAttribute(comp, name="Offset Position", value=Vector3ToString(shapeOffset))

    # Names of Blender selected objects
    selectedNames = []
    for obj in context.selected_objects:
        selectedNames.append(obj.name)

    # Export full scene: scene elements + scene node
    if sOptions.doFullScene: 
        filepath = GetFilepath(PathType.SCENES, uScene.blenderSceneName, fOptions)
        if CheckFilepath(filepath[0], fOptions):
            log.info( "Creating full scene {:s}".format(filepath[1]) )
            WriteXmlFile(root, filepath[0], fOptions)

    # Export a collective node
    if sOptions.doCollectivePrefab:
        rootNodeCopy = copy.deepcopy(rootNode)      
        if sOptions.onlySelected:
            # Get the IDs of the node of the selected objects
            selectedIds = []
            for blenderName, xmlNode in xmlNodes.items():
                if blenderName in selectedNames:
                    selectedIds.append(xmlNode.get("id", None))
            # Keep only the nodes with the attribute "id" in the list
            XmlNodeFilter(rootNodeCopy, "id", selectedIds)

        XmlIdSet(rootNodeCopy)
        filepath = GetFilepath(PathType.OBJECTS, uScene.blenderSceneName, fOptions)
        if CheckFilepath(filepath[0], fOptions):
            log.info( "Creating collective prefab {:s}".format(filepath[1]) )
            WriteXmlFile(rootNodeCopy, filepath[0], fOptions)

    # Export objects nodes (including their children)
    if sOptions.doObjectsPrefab:
        usedNames = []
        noObject = True
        for blenderName, xmlNode in xmlNodes.items():
            # Filter selected objects
            if sOptions.onlySelected and not blenderName in selectedNames: 
                continue
            noObject = False
            # From Blender name to plain name, this is useful for LODs but we can have 
            # duplicates, in that case fallback to the Blender name
            name = None
            for uSceneModel in uScene.modelsList:
                if uSceneModel.blenderName == blenderName:
                    name = uSceneModel.name
                    break
            if not name or name in usedNames:
                name = blenderName
            usedNames.append(name)

            XmlIdSet(xmlNode)
            filepath = GetFilepath(PathType.OBJECTS, name, fOptions)
            if CheckFilepath(filepath[0], fOptions):
                log.info( "Creating object prefab {:s}".format(filepath[1]) )
                WriteXmlFile(xmlNode, filepath[0], fOptions)
        if noObject:
            log.warning("No object selected for prefab export")
