module IMODESaveFile where

open import Data.String
open import Data.List

projectXmlString : String
projectXmlString = "<project id=\"1696681038889_1\" name=\"ExampleIMODESave\">
    <submodels>
        <model path=\"logicModel1.mdlx\" hash=\"\"/>
    </submodels>
    <types path=\"Types.typx\"/>
    <constants path=\"Constants.constx\"/>
    <interfaces path=\"Interfaces.intrfx\"/>
    <ports path=\"Ports.portx\"/>
    <packages/>
    <Refs/>
    <configurations>
        <configuration path=\"ExampleIMODESave.confx\"/>
    </configurations>
    <version createdVer=\"0.011.6701\" modifiedVer=\"0.011.6701\"/>
    <requirement reqCounter=\"0\"/>
</project>"

typesXmlString : String
typesXmlString = "<types>
    <type name=\"Type1\" isTypeTemp=\"0\" definition=\"&lt;array&gt;\" comment=\"\">
        <arrayInfo name=\"\" isTypeTemp=\"0\" definition=\"int16\" comment=\"\">
            <dimensions>
                <dimension>3</dimension>
                <dimension>2</dimension>
            </dimensions>
        </arrayInfo>
    </type>
    <type name=\"Type2\" isTypeTemp=\"0\" definition=\"&lt;enumeration&gt;\" comment=\"\">
        <definitionElements>
            <definitionElement value=\"value1\" comment=\"\"/>
            <definitionElement value=\"value2\" comment=\"\"/>
        </definitionElements>
    </type>
    <type name=\"Type3\" isTypeTemp=\"0\" definition=\"&lt;structure&gt;\" comment=\"\">
        <definitionElements>
            <definitionElement name=\"label1\" isTypeTemp=\"0\" definition=\"uint8\" comment=\"\"/>
            <definitionElement name=\"label2\" isTypeTemp=\"0\" definition=\"char\" comment=\"\"/>
            <definitionElement name=\"label3\" isTypeTemp=\"0\" definition=\"Type1\" comment=\"\"/>
        </definitionElements>
    </type>
    <type name=\"Type4\" isTypeTemp=\"0\" definition=\"Type2\" comment=\"\"/>
</types>"

interfacesXmlString : String
interfacesXmlString = "<interfaces>
    <interface name=\"Interface1\" isTypeTemp=\"0\" definition=\"int32\" comment=\"\" IO=\"0\" Flag=\"0\" value=\"0\"/>
    <interface name=\"Interface2\" isTypeTemp=\"0\" definition=\"Type2\" comment=\"\" IO=\"0\" Flag=\"0\" value=\"\"/>
</interfaces>"

constantsXmlString : String
constantsXmlString = "<constants>
    <constant name=\"Constant1\" isTypeTemp=\"0\" definition=\"Type1\" comment=\"\" value=\"[[0, 0], [0, 0], [0, 0]]\"/>
    <constant name=\"Constant2\" isTypeTemp=\"0\" definition=\"int8\" comment=\"\" value=\"0\"/>
    <constant name=\"Constant3\" isTypeTemp=\"0\" definition=\"Type2\" comment=\"\" value=\"value1\"/>
    <constant name=\"Constant4\" isTypeTemp=\"0\" definition=\"Type3\" comment=\"\" value=\"{label1 : 0, label2 : ' ', label3 : [[0, 0], [0, 0], [0, 0]]}\"/>
</constants>"

modelXmlStrings : List String
modelXmlStrings = "<model tracedRequirements=\"\" id=\"1696681108403_1\" name=\"logicModel1\" projectFileName=\"ExampleIMODESave.prjx\" description=\"\" hash=\"a67070cb51e7193b57ee8ad63c72b3f5\">
    <submodels>
        <model tracedRequirements=\"\" visibility=\"1\" enable=\"1\" id=\"1696681110644_1\" name=\"Input1\" projectFileName=\"\" description=\"\" hash=\"47652e68b75f740d7c4228759d31a8f5\">
            <submodels/>
            <ioDirection value=\"0\"/>
            <center yCoord=\"-58\" xCoord=\"-400\"/>
            <size height=\"40\" width=\"60\"/>
            <inputConnections/>
            <outputConnections>
                <outputConnection connectedTo=\"1696681114575_1\" portOrder=\"0\"/>
            </outputConnections>
            <conditionConnections/>
            <parameterConnections/>
            <copyOf value=\"1696681110711_2\"/>
            <last last=\"0\"/>
            <value value=\"0\"/>
        </model>
        <model tracedRequirements=\"\" visibility=\"1\" enable=\"1\" id=\"1696681112129_3\" name=\"Input3\" projectFileName=\"\" description=\"\" hash=\"47652e68b75f740d7c4228759d31a8f5\">
            <submodels/>
            <ioDirection value=\"0\"/>
            <center yCoord=\"43\" xCoord=\"-403\"/>
            <size height=\"40\" width=\"60\"/>
            <inputConnections/>
            <outputConnections>
                <outputConnection connectedTo=\"1696681115337_2\" portOrder=\"0\"/>
            </outputConnections>
            <conditionConnections/>
            <parameterConnections/>
            <copyOf value=\"1696681112176_4\"/>
            <last last=\"0\"/>
            <value value=\"0\"/>
        </model>
        <model tracedRequirements=\"\" visibility=\"1\" enable=\"1\" id=\"1696681114187_1\" name=\"Addition1\" projectFileName=\"\" description=\"\" hash=\"955ca6d568f93954497d59e165f9fa9b\">
            <submodels/>
            <ioDirection value=\"0\"/>
            <center yCoord=\"-1\" xCoord=\"-271\"/>
            <size height=\"40\" width=\"60\"/>
            <inputConnections>
                <inputConnection connectedTo=\"1696681114575_1\" portOrder=\"0\"/>
                <inputConnection connectedTo=\"1696681115337_2\" portOrder=\"1\"/>
            </inputConnections>
            <outputConnections>
                <outputConnection connectedTo=\"1696681118357_3\" portOrder=\"0\"/>
            </outputConnections>
            <conditionConnections/>
            <parameterConnections/>
        </model>
        <model tracedRequirements=\"\" visibility=\"1\" enable=\"1\" id=\"1696681114575_1\" name=\"Connect1\" projectFileName=\"\" description=\"\" hash=\"c2459d3d1ef8a0b20f3e7125bae74582\">
            <submodels/>
            <startOperation yCoord=\"-58\" xCoord=\"-370\" connectedTo=\"1696681110644_1\"/>
            <endOperation yCoord=\"-7.666666666666666\" xCoord=\"-301\" connectedTo=\"1696681114187_1\"/>
            <points>
                <point yCoord=\"-58\" xCoord=\"-370\"/>
                <point yCoord=\"-58\" xCoord=\"-337\"/>
                <point yCoord=\"-7.666666666666666\" xCoord=\"-337\"/>
                <point yCoord=\"-7.666666666666666\" xCoord=\"-301\"/>
            </points>
            <type name=\"int16\"/>
        </model>
        <model tracedRequirements=\"\" visibility=\"1\" enable=\"1\" id=\"1696681115337_2\" name=\"Connect2\" projectFileName=\"\" description=\"\" hash=\"c2459d3d1ef8a0b20f3e7125bae74582\">
            <submodels/>
            <startOperation yCoord=\"43\" xCoord=\"-373\" connectedTo=\"1696681112129_3\"/>
            <endOperation yCoord=\"5.666666666666668\" xCoord=\"-301\" connectedTo=\"1696681114187_1\"/>
            <points>
                <point yCoord=\"43\" xCoord=\"-373\"/>
                <point yCoord=\"43\" xCoord=\"-353\"/>
                <point yCoord=\"5.666666666666668\" xCoord=\"-353\"/>
                <point yCoord=\"5.666666666666668\" xCoord=\"-301\"/>
            </points>
            <type name=\"int16\"/>
        </model>
        <model tracedRequirements=\"\" visibility=\"1\" enable=\"1\" id=\"1696681118011_1\" name=\"Output1\" projectFileName=\"\" description=\"\" hash=\"1deb5a48a4655393a18760b265134ef3\">
            <submodels/>
            <ioDirection value=\"0\"/>
            <center yCoord=\"-6\" xCoord=\"-98\"/>
            <size height=\"40\" width=\"60\"/>
            <inputConnections>
                <inputConnection connectedTo=\"1696681118357_3\" portOrder=\"0\"/>
            </inputConnections>
            <outputConnections/>
            <conditionConnections/>
            <parameterConnections/>
            <copyOf value=\"1696681118077_2\"/>
            <last last=\"0\"/>
        </model>
        <model tracedRequirements=\"\" visibility=\"1\" enable=\"1\" id=\"1696681118357_3\" name=\"Connect3\" projectFileName=\"\" description=\"\" hash=\"c2459d3d1ef8a0b20f3e7125bae74582\">
            <submodels/>
            <startOperation yCoord=\"-1\" xCoord=\"-241\" connectedTo=\"1696681114187_1\"/>
            <endOperation yCoord=\"-6\" xCoord=\"-128\" connectedTo=\"1696681118011_1\"/>
            <points>
                <point yCoord=\"-1\" xCoord=\"-241\"/>
                <point yCoord=\"-1\" xCoord=\"-190\"/>
                <point yCoord=\"-6\" xCoord=\"-190\"/>
                <point yCoord=\"-6\" xCoord=\"-128\"/>
            </points>
            <type name=\"int16\"/>
        </model>
        <model tracedRequirements=\"\" visibility=\"1\" enable=\"1\" id=\"1696681110711_2\" name=\"Input1\" projectFileName=\"\" description=\"\" hash=\"47652e68b75f740d7c4228759d31a8f5\">
            <submodels/>
            <type name=\"int16\"/>
            <sourceInstance value=\"1\"/>
            <last value=\"\"/>
            <default value=\"\"/>
            <value value=\"0\"/>
        </model>
        <model tracedRequirements=\"\" visibility=\"1\" enable=\"1\" id=\"1696681112176_4\" name=\"Input3\" projectFileName=\"\" description=\"\" hash=\"47652e68b75f740d7c4228759d31a8f5\">
            <submodels/>
            <type name=\"int16\"/>
            <sourceInstance value=\"1\"/>
            <last value=\"\"/>
            <default value=\"\"/>
            <value value=\"0\"/>
        </model>
        <model tracedRequirements=\"\" visibility=\"1\" enable=\"1\" id=\"1696681118077_2\" name=\"Output1\" projectFileName=\"\" description=\"\" hash=\"1deb5a48a4655393a18760b265134ef3\">
            <submodels/>
            <type name=\"int16\"/>
            <sourceInstance value=\"1\"/>
            <last value=\"\"/>
            <default value=\"\"/>
        </model>
    </submodels>
    <genericTypes/>
    <sizeParameters/>
    <startModels>
        <startModel hash=\"1696681110711_2\"/>
        <startModel hash=\"1696681112176_4\"/>
    </startModels>
    <endModels>
        <endModel hash=\"1696681118077_2\"/>
    </endModels>
    <inputSensors/>
    <outputSensors/>
    <locals/>
    <lookups/>
</model>" ∷ []
