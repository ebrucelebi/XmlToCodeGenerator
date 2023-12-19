{-# OPTIONS --safe #-}

module IMODESaveFile where

open import Data.String
open import Data.List

projectXmlString : String
projectXmlString = "<project id=\"1696681038889_1\" name=\"ExampleIMODESave\">
    <submodels>
        <model path=\"logicModel1.mdlx\" hash=\"\"/>
        <model path=\"hasCycle.mdlx\" hash=\"\"/>
        <model path=\"hasCycle2.mdlx\" hash=\"\"/>
        <model path=\"doubleOutput.mdlx\" hash=\"\"/>
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
    <type name=\"Type5\" isTypeTemp=\"0\" definition=\"int32\" comment=\"\"/>
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

modelStringThatHasCycle : String
modelStringThatHasCycle = "<model tracedRequirements=\"\" description=\"\" id=\"1702980085738_3\" name=\"hasCycle\" hash=\"a67070cb51e7193b57ee8ad63c72b3f5\" projectFileName=\"ExampleIMODESave.prjx\">
    <submodels>
        <model tracedRequirements=\"\" description=\"\" id=\"1702980090841_7\" name=\"Input7\" hash=\"47652e68b75f740d7c4228759d31a8f5\" projectFileName=\"\" enable=\"1\" visibility=\"1\">
            <submodels/>
            <ioDirection value=\"0\"/>
            <center yCoord=\"-99\" xCoord=\"-282\"/>
            <size width=\"60\" height=\"40\"/>
            <inputConnections/>
            <outputConnections>
                <outputConnection connectedTo=\"1702980106934_9\" portOrder=\"0\"/>
            </outputConnections>
            <conditionConnections/>
            <parameterConnections/>
            <copyOf value=\"1702980090917_8\"/>
            <last last=\"0\"/>
            <value value=\"0\"/>
        </model>
        <model tracedRequirements=\"\" description=\"\" id=\"1702980093845_3\" name=\"Addition3\" hash=\"955ca6d568f93954497d59e165f9fa9b\" projectFileName=\"\" enable=\"1\" visibility=\"1\">
            <submodels/>
            <ioDirection value=\"0\"/>
            <center yCoord=\"-73\" xCoord=\"-146\"/>
            <size width=\"60\" height=\"40\"/>
            <inputConnections>
                <inputConnection connectedTo=\"1702980106934_9\" portOrder=\"0\"/>
                <inputConnection connectedTo=\"1702980107873_10\" portOrder=\"1\"/>
            </inputConnections>
            <outputConnections>
                <outputConnection connectedTo=\"1702980106161_8\" portOrder=\"0\"/>
                <outputConnection connectedTo=\"1702980107873_10\" portOrder=\"0\"/>
            </outputConnections>
            <conditionConnections/>
            <parameterConnections/>
        </model>
        <model tracedRequirements=\"\" description=\"\" id=\"1702980105745_5\" name=\"Output5\" hash=\"1deb5a48a4655393a18760b265134ef3\" projectFileName=\"\" enable=\"1\" visibility=\"1\">
            <submodels/>
            <ioDirection value=\"0\"/>
            <center yCoord=\"-67\" xCoord=\"22\"/>
            <size width=\"60\" height=\"40\"/>
            <inputConnections>
                <inputConnection connectedTo=\"1702980106161_8\" portOrder=\"0\"/>
            </inputConnections>
            <outputConnections/>
            <conditionConnections/>
            <parameterConnections/>
            <copyOf value=\"1702980105810_6\"/>
            <last last=\"0\"/>
        </model>
        <model tracedRequirements=\"\" description=\"\" id=\"1702980106161_8\" name=\"Connect8\" hash=\"c2459d3d1ef8a0b20f3e7125bae74582\" projectFileName=\"\" enable=\"1\" visibility=\"1\">
            <submodels/>
            <startOperation yCoord=\"-73\" connectedTo=\"1702980093845_3\" xCoord=\"-116\"/>
            <endOperation yCoord=\"-67\" connectedTo=\"1702980105745_5\" xCoord=\"-8\"/>
            <points>
                <point yCoord=\"-73\" xCoord=\"-116\"/>
                <point yCoord=\"-73\" xCoord=\"-28\"/>
                <point yCoord=\"-67\" xCoord=\"-28\"/>
                <point yCoord=\"-67\" xCoord=\"-8\"/>
            </points>
            <type name=\"int16\"/>
        </model>
        <model tracedRequirements=\"\" description=\"\" id=\"1702980106934_9\" name=\"Connect9\" hash=\"c2459d3d1ef8a0b20f3e7125bae74582\" projectFileName=\"\" enable=\"1\" visibility=\"1\">
            <submodels/>
            <startOperation yCoord=\"-99\" connectedTo=\"1702980090841_7\" xCoord=\"-252\"/>
            <endOperation yCoord=\"-79.66666666666667\" connectedTo=\"1702980093845_3\" xCoord=\"-176\"/>
            <points>
                <point yCoord=\"-99\" xCoord=\"-252\"/>
                <point yCoord=\"-99\" xCoord=\"-199\"/>
                <point yCoord=\"-79.66666666666667\" xCoord=\"-199\"/>
                <point yCoord=\"-79.66666666666667\" xCoord=\"-176\"/>
            </points>
            <type name=\"int16\"/>
        </model>
        <model tracedRequirements=\"\" description=\"\" id=\"1702980107873_10\" name=\"Connect10\" hash=\"c2459d3d1ef8a0b20f3e7125bae74582\" projectFileName=\"\" enable=\"1\" visibility=\"1\">
            <submodels/>
            <startOperation yCoord=\"-73\" connectedTo=\"1702980093845_3\" xCoord=\"-116\"/>
            <endOperation yCoord=\"-66.33333333333333\" connectedTo=\"1702980093845_3\" xCoord=\"-176\"/>
            <points>
                <point yCoord=\"-73\" xCoord=\"-116\"/>
                <point yCoord=\"-73\" xCoord=\"-38\"/>
                <point yCoord=\"58\" xCoord=\"-38\"/>
                <point yCoord=\"58\" xCoord=\"-242\"/>
                <point yCoord=\"40\" xCoord=\"-242\"/>
                <point yCoord=\"40\" xCoord=\"-265\"/>
                <point yCoord=\"-66.33333333333333\" xCoord=\"-265\"/>
                <point yCoord=\"-66.33333333333333\" xCoord=\"-176\"/>
            </points>
            <type name=\"int16\"/>
        </model>
        <model tracedRequirements=\"\" description=\"\" id=\"1702980090917_8\" name=\"Input7\" hash=\"47652e68b75f740d7c4228759d31a8f5\" projectFileName=\"\" enable=\"1\" visibility=\"1\">
            <submodels/>
            <type name=\"int16\"/>
            <sourceInstance value=\"1\"/>
            <last value=\"\"/>
            <default value=\"\"/>
            <value value=\"0\"/>
        </model>
        <model tracedRequirements=\"\" description=\"\" id=\"1702980105810_6\" name=\"Output5\" hash=\"1deb5a48a4655393a18760b265134ef3\" projectFileName=\"\" enable=\"1\" visibility=\"1\">
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
        <startModel hash=\"1702980090917_8\"/>
    </startModels>
    <endModels>
        <endModel hash=\"1702980105810_6\"/>
    </endModels>
    <inputSensors/>
    <outputSensors/>
    <locals/>
    <lookups/>
</model>"

modelStringThatHasCycle2 : String
modelStringThatHasCycle2 = "<model tracedRequirements=\"\" description=\"\" id=\"1702980350451_4\" name=\"hasCycle2\" hash=\"a67070cb51e7193b57ee8ad63c72b3f5\" projectFileName=\"ExampleIMODESave.prjx\">
    <submodels>
        <model tracedRequirements=\"\" description=\"\" id=\"1702980358768_9\" name=\"Input9\" hash=\"47652e68b75f740d7c4228759d31a8f5\" projectFileName=\"\" enable=\"1\" visibility=\"1\">
            <submodels/>
            <ioDirection value=\"0\"/>
            <center yCoord=\"-119\" xCoord=\"-350\"/>
            <size width=\"60\" height=\"40\"/>
            <inputConnections/>
            <outputConnections>
                <outputConnection connectedTo=\"1702980381220_13\" portOrder=\"0\"/>
            </outputConnections>
            <conditionConnections/>
            <parameterConnections/>
            <copyOf value=\"1702980358820_10\"/>
            <last last=\"0\"/>
            <value value=\"0\"/>
        </model>
        <model tracedRequirements=\"\" description=\"\" id=\"1702980359718_4\" name=\"Addition4\" hash=\"955ca6d568f93954497d59e165f9fa9b\" projectFileName=\"\" enable=\"1\" visibility=\"1\">
            <submodels/>
            <ioDirection value=\"0\"/>
            <center yCoord=\"-110\" xCoord=\"-155\"/>
            <size width=\"60\" height=\"40\"/>
            <inputConnections>
                <inputConnection connectedTo=\"1702980381220_13\" portOrder=\"0\"/>
                <inputConnection connectedTo=\"1702980391184_15\" portOrder=\"1\"/>
            </inputConnections>
            <outputConnections>
                <outputConnection connectedTo=\"1702980379810_12\" portOrder=\"0\"/>
                <outputConnection connectedTo=\"1702980388605_14\" portOrder=\"0\"/>
            </outputConnections>
            <conditionConnections/>
            <parameterConnections/>
        </model>
        <model tracedRequirements=\"\" description=\"\" id=\"1702980360884_5\" name=\"Addition5\" hash=\"955ca6d568f93954497d59e165f9fa9b\" projectFileName=\"\" enable=\"1\" visibility=\"1\">
            <submodels/>
            <ioDirection value=\"0\"/>
            <center yCoord=\"-88\" xCoord=\"80\"/>
            <size width=\"60\" height=\"40\"/>
            <inputConnections>
                <inputConnection connectedTo=\"1702980379810_12\" portOrder=\"0\"/>
                <inputConnection connectedTo=\"1702980388605_14\" portOrder=\"1\"/>
            </inputConnections>
            <outputConnections>
                <outputConnection connectedTo=\"1702980364216_11\" portOrder=\"0\"/>
                <outputConnection connectedTo=\"1702980391184_15\" portOrder=\"0\"/>
            </outputConnections>
            <conditionConnections/>
            <parameterConnections/>
        </model>
        <model tracedRequirements=\"\" description=\"\" id=\"1702980363784_7\" name=\"Output7\" hash=\"1deb5a48a4655393a18760b265134ef3\" projectFileName=\"\" enable=\"1\" visibility=\"1\">
            <submodels/>
            <ioDirection value=\"0\"/>
            <center yCoord=\"-44\" xCoord=\"282\"/>
            <size width=\"60\" height=\"40\"/>
            <inputConnections>
                <inputConnection connectedTo=\"1702980364216_11\" portOrder=\"0\"/>
            </inputConnections>
            <outputConnections/>
            <conditionConnections/>
            <parameterConnections/>
            <copyOf value=\"1702980363847_8\"/>
            <last last=\"0\"/>
        </model>
        <model tracedRequirements=\"\" description=\"\" id=\"1702980364216_11\" name=\"Connect11\" hash=\"c2459d3d1ef8a0b20f3e7125bae74582\" projectFileName=\"\" enable=\"1\" visibility=\"1\">
            <submodels/>
            <startOperation yCoord=\"-88\" connectedTo=\"1702980360884_5\" xCoord=\"110\"/>
            <endOperation yCoord=\"-44\" connectedTo=\"1702980363784_7\" xCoord=\"252\"/>
            <points>
                <point yCoord=\"-88\" xCoord=\"110\"/>
                <point yCoord=\"-88\" xCoord=\"232\"/>
                <point yCoord=\"-44\" xCoord=\"232\"/>
                <point yCoord=\"-44\" xCoord=\"252\"/>
            </points>
            <type name=\"int16\"/>
        </model>
        <model tracedRequirements=\"\" description=\"\" id=\"1702980379810_12\" name=\"Connect12\" hash=\"c2459d3d1ef8a0b20f3e7125bae74582\" projectFileName=\"\" enable=\"1\" visibility=\"1\">
            <submodels/>
            <startOperation yCoord=\"-110\" connectedTo=\"1702980359718_4\" xCoord=\"-125\"/>
            <endOperation yCoord=\"-94.66666666666667\" connectedTo=\"1702980360884_5\" xCoord=\"50\"/>
            <points>
                <point yCoord=\"-110\" xCoord=\"-125\"/>
                <point yCoord=\"-110\" xCoord=\"30\"/>
                <point yCoord=\"-94.66666666666667\" xCoord=\"30\"/>
                <point yCoord=\"-94.66666666666667\" xCoord=\"50\"/>
            </points>
            <type name=\"int16\"/>
        </model>
        <model tracedRequirements=\"\" description=\"\" id=\"1702980381220_13\" name=\"Connect13\" hash=\"c2459d3d1ef8a0b20f3e7125bae74582\" projectFileName=\"\" enable=\"1\" visibility=\"1\">
            <submodels/>
            <startOperation yCoord=\"-119\" connectedTo=\"1702980358768_9\" xCoord=\"-320\"/>
            <endOperation yCoord=\"-116.66666666666667\" connectedTo=\"1702980359718_4\" xCoord=\"-185\"/>
            <points>
                <point yCoord=\"-119\" xCoord=\"-320\"/>
                <point yCoord=\"-119\" xCoord=\"-205\"/>
                <point yCoord=\"-116.66666666666667\" xCoord=\"-205\"/>
                <point yCoord=\"-116.66666666666667\" xCoord=\"-185\"/>
            </points>
            <type name=\"int16\"/>
        </model>
        <model tracedRequirements=\"\" description=\"\" id=\"1702980388605_14\" name=\"Connect14\" hash=\"c2459d3d1ef8a0b20f3e7125bae74582\" projectFileName=\"\" enable=\"1\" visibility=\"1\">
            <submodels/>
            <startOperation yCoord=\"-110\" connectedTo=\"1702980359718_4\" xCoord=\"-125\"/>
            <endOperation yCoord=\"-81.33333333333333\" connectedTo=\"1702980360884_5\" xCoord=\"50\"/>
            <points>
                <point yCoord=\"-110\" xCoord=\"-125\"/>
                <point yCoord=\"-110\" xCoord=\"-24\"/>
                <point yCoord=\"-81.33333333333333\" xCoord=\"-24\"/>
                <point yCoord=\"-81.33333333333333\" xCoord=\"50\"/>
            </points>
            <type name=\"int16\"/>
        </model>
        <model tracedRequirements=\"\" description=\"\" id=\"1702980391184_15\" name=\"Connect15\" hash=\"c2459d3d1ef8a0b20f3e7125bae74582\" projectFileName=\"\" enable=\"1\" visibility=\"1\">
            <submodels/>
            <startOperation yCoord=\"-88\" connectedTo=\"1702980360884_5\" xCoord=\"110\"/>
            <endOperation yCoord=\"-103.33333333333333\" connectedTo=\"1702980359718_4\" xCoord=\"-185\"/>
            <points>
                <point yCoord=\"-88\" xCoord=\"110\"/>
                <point yCoord=\"-88\" xCoord=\"138\"/>
                <point yCoord=\"14\" xCoord=\"138\"/>
                <point yCoord=\"14\" xCoord=\"-245\"/>
                <point yCoord=\"-103.33333333333333\" xCoord=\"-245\"/>
                <point yCoord=\"-103.33333333333333\" xCoord=\"-185\"/>
            </points>
            <type name=\"int16\"/>
        </model>
        <model tracedRequirements=\"\" description=\"\" id=\"1702980358820_10\" name=\"Input9\" hash=\"47652e68b75f740d7c4228759d31a8f5\" projectFileName=\"\" enable=\"1\" visibility=\"1\">
            <submodels/>
            <type name=\"int16\"/>
            <sourceInstance value=\"1\"/>
            <last value=\"\"/>
            <default value=\"\"/>
            <value value=\"0\"/>
        </model>
        <model tracedRequirements=\"\" description=\"\" id=\"1702980363847_8\" name=\"Output7\" hash=\"1deb5a48a4655393a18760b265134ef3\" projectFileName=\"\" enable=\"1\" visibility=\"1\">
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
        <startModel hash=\"1702980358820_10\"/>
    </startModels>
    <endModels>
        <endModel hash=\"1702980363847_8\"/>
    </endModels>
    <inputSensors/>
    <outputSensors/>
    <locals/>
    <lookups/>
</model>"

doubleOutput : String
doubleOutput = "<model tracedRequirements=\"\" description=\"\" id=\"1702982513357_5\" name=\"doubleOutput\" hash=\"a67070cb51e7193b57ee8ad63c72b3f5\" projectFileName=\"ExampleIMODESave.prjx\">
    <submodels>
        <model tracedRequirements=\"\" description=\"\" id=\"1702982541825_11\" name=\"Input11\" hash=\"47652e68b75f740d7c4228759d31a8f5\" projectFileName=\"\" enable=\"1\" visibility=\"1\">
            <submodels/>
            <ioDirection value=\"0\"/>
            <center yCoord=\"-136\" xCoord=\"-395\"/>
            <size width=\"60\" height=\"40\"/>
            <inputConnections/>
            <outputConnections>
                <outputConnection connectedTo=\"1702982548262_16\" portOrder=\"0\"/>
            </outputConnections>
            <conditionConnections/>
            <parameterConnections/>
            <copyOf value=\"1702982541890_12\"/>
            <last last=\"0\"/>
            <value value=\"0\"/>
        </model>
        <model tracedRequirements=\"\" description=\"\" id=\"1702982542875_13\" name=\"Input13\" hash=\"47652e68b75f740d7c4228759d31a8f5\" projectFileName=\"\" enable=\"1\" visibility=\"1\">
            <submodels/>
            <ioDirection value=\"0\"/>
            <center yCoord=\"-6\" xCoord=\"-407\"/>
            <size width=\"60\" height=\"40\"/>
            <inputConnections/>
            <outputConnections>
                <outputConnection connectedTo=\"1702982549172_17\" portOrder=\"0\"/>
                <outputConnection connectedTo=\"1702982551338_19\" portOrder=\"0\"/>
            </outputConnections>
            <conditionConnections/>
            <parameterConnections/>
            <copyOf value=\"1702982542944_14\"/>
            <last last=\"0\"/>
            <value value=\"0\"/>
        </model>
        <model tracedRequirements=\"\" description=\"\" id=\"1702982544232_6\" name=\"Addition6\" hash=\"955ca6d568f93954497d59e165f9fa9b\" projectFileName=\"\" enable=\"1\" visibility=\"1\">
            <submodels/>
            <ioDirection value=\"0\"/>
            <center yCoord=\"-94\" xCoord=\"-182\"/>
            <size width=\"60\" height=\"40\"/>
            <inputConnections>
                <inputConnection connectedTo=\"1702982548262_16\" portOrder=\"0\"/>
                <inputConnection connectedTo=\"1702982549172_17\" portOrder=\"1\"/>
            </inputConnections>
            <outputConnections>
                <outputConnection connectedTo=\"1702982549830_18\" portOrder=\"0\"/>
                <outputConnection connectedTo=\"1702982558161_20\" portOrder=\"0\"/>
            </outputConnections>
            <conditionConnections/>
            <parameterConnections/>
        </model>
        <model tracedRequirements=\"\" description=\"\" id=\"1702982546543_1\" name=\"Multiplication1\" hash=\"c242c66d2b427ca579e166bcb7d29e13\" projectFileName=\"\" enable=\"1\" visibility=\"1\">
            <submodels/>
            <ioDirection value=\"0\"/>
            <center yCoord=\"-38\" xCoord=\"-7\"/>
            <size width=\"60\" height=\"40\"/>
            <inputConnections>
                <inputConnection connectedTo=\"1702982549830_18\" portOrder=\"0\"/>
                <inputConnection connectedTo=\"1702982551338_19\" portOrder=\"1\"/>
            </inputConnections>
            <outputConnections>
                <outputConnection connectedTo=\"1702982559195_21\" portOrder=\"0\"/>
            </outputConnections>
            <conditionConnections/>
            <parameterConnections/>
        </model>
        <model tracedRequirements=\"\" description=\"\" id=\"1702982548262_16\" name=\"Connect16\" hash=\"c2459d3d1ef8a0b20f3e7125bae74582\" projectFileName=\"\" enable=\"1\" visibility=\"1\">
            <submodels/>
            <startOperation yCoord=\"-136\" connectedTo=\"1702982541825_11\" xCoord=\"-365\"/>
            <endOperation yCoord=\"-100.66666666666667\" connectedTo=\"1702982544232_6\" xCoord=\"-212\"/>
            <points>
                <point yCoord=\"-136\" xCoord=\"-365\"/>
                <point yCoord=\"-136\" xCoord=\"-233\"/>
                <point yCoord=\"-100.66666666666667\" xCoord=\"-233\"/>
                <point yCoord=\"-100.66666666666667\" xCoord=\"-212\"/>
            </points>
            <type name=\"int16\"/>
        </model>
        <model tracedRequirements=\"\" description=\"\" id=\"1702982549172_17\" name=\"Connect17\" hash=\"c2459d3d1ef8a0b20f3e7125bae74582\" projectFileName=\"\" enable=\"1\" visibility=\"1\">
            <submodels/>
            <startOperation yCoord=\"-6\" connectedTo=\"1702982542875_13\" xCoord=\"-377\"/>
            <endOperation yCoord=\"-87.33333333333333\" connectedTo=\"1702982544232_6\" xCoord=\"-212\"/>
            <points>
                <point yCoord=\"-6\" xCoord=\"-377\"/>
                <point yCoord=\"-6\" xCoord=\"-233\"/>
                <point yCoord=\"-87.33333333333333\" xCoord=\"-233\"/>
                <point yCoord=\"-87.33333333333333\" xCoord=\"-212\"/>
            </points>
            <type name=\"int16\"/>
        </model>
        <model tracedRequirements=\"\" description=\"\" id=\"1702982549830_18\" name=\"Connect18\" hash=\"c2459d3d1ef8a0b20f3e7125bae74582\" projectFileName=\"\" enable=\"1\" visibility=\"1\">
            <submodels/>
            <startOperation yCoord=\"-94\" connectedTo=\"1702982544232_6\" xCoord=\"-152\"/>
            <endOperation yCoord=\"-44.666666666666664\" connectedTo=\"1702982546543_1\" xCoord=\"-37\"/>
            <points>
                <point yCoord=\"-94\" xCoord=\"-152\"/>
                <point yCoord=\"-94\" xCoord=\"-103\"/>
                <point yCoord=\"-44.666666666666664\" xCoord=\"-103\"/>
                <point yCoord=\"-44.666666666666664\" xCoord=\"-37\"/>
            </points>
            <type name=\"int16\"/>
        </model>
        <model tracedRequirements=\"\" description=\"\" id=\"1702982551338_19\" name=\"Connect19\" hash=\"c2459d3d1ef8a0b20f3e7125bae74582\" projectFileName=\"\" enable=\"1\" visibility=\"1\">
            <submodels/>
            <startOperation yCoord=\"-6\" connectedTo=\"1702982542875_13\" xCoord=\"-377\"/>
            <endOperation yCoord=\"-31.333333333333332\" connectedTo=\"1702982546543_1\" xCoord=\"-37\"/>
            <points>
                <point yCoord=\"-6\" xCoord=\"-377\"/>
                <point yCoord=\"-6\" xCoord=\"-103\"/>
                <point yCoord=\"-31.333333333333332\" xCoord=\"-103\"/>
                <point yCoord=\"-31.333333333333332\" xCoord=\"-37\"/>
            </points>
            <type name=\"int16\"/>
        </model>
        <model tracedRequirements=\"\" description=\"\" id=\"1702982555559_9\" name=\"Output9\" hash=\"1deb5a48a4655393a18760b265134ef3\" projectFileName=\"\" enable=\"1\" visibility=\"1\">
            <submodels/>
            <ioDirection value=\"0\"/>
            <center yCoord=\"-134\" xCoord=\"-18\"/>
            <size width=\"60\" height=\"40\"/>
            <inputConnections>
                <inputConnection connectedTo=\"1702982558161_20\" portOrder=\"0\"/>
            </inputConnections>
            <outputConnections/>
            <conditionConnections/>
            <parameterConnections/>
            <copyOf value=\"1702982555602_10\"/>
            <last last=\"0\"/>
        </model>
        <model tracedRequirements=\"\" description=\"\" id=\"1702982556907_11\" name=\"Output11\" hash=\"1deb5a48a4655393a18760b265134ef3\" projectFileName=\"\" enable=\"1\" visibility=\"1\">
            <submodels/>
            <ioDirection value=\"0\"/>
            <center yCoord=\"-43\" xCoord=\"104\"/>
            <size width=\"60\" height=\"40\"/>
            <inputConnections>
                <inputConnection connectedTo=\"1702982559195_21\" portOrder=\"0\"/>
            </inputConnections>
            <outputConnections/>
            <conditionConnections/>
            <parameterConnections/>
            <copyOf value=\"1702982556952_12\"/>
            <last last=\"0\"/>
        </model>
        <model tracedRequirements=\"\" description=\"\" id=\"1702982558161_20\" name=\"Connect20\" hash=\"c2459d3d1ef8a0b20f3e7125bae74582\" projectFileName=\"\" enable=\"1\" visibility=\"1\">
            <submodels/>
            <startOperation yCoord=\"-94\" connectedTo=\"1702982544232_6\" xCoord=\"-152\"/>
            <endOperation yCoord=\"-134\" connectedTo=\"1702982555559_9\" xCoord=\"-48\"/>
            <points>
                <point yCoord=\"-94\" xCoord=\"-152\"/>
                <point yCoord=\"-94\" xCoord=\"-132\"/>
                <point yCoord=\"-134\" xCoord=\"-132\"/>
                <point yCoord=\"-134\" xCoord=\"-48\"/>
            </points>
            <type name=\"int16\"/>
        </model>
        <model tracedRequirements=\"\" description=\"\" id=\"1702982559195_21\" name=\"Connect21\" hash=\"c2459d3d1ef8a0b20f3e7125bae74582\" projectFileName=\"\" enable=\"1\" visibility=\"1\">
            <submodels/>
            <startOperation yCoord=\"-38\" connectedTo=\"1702982546543_1\" xCoord=\"23\"/>
            <endOperation yCoord=\"-43\" connectedTo=\"1702982556907_11\" xCoord=\"74\"/>
            <points>
                <point yCoord=\"-38\" xCoord=\"23\"/>
                <point yCoord=\"-38\" xCoord=\"43\"/>
                <point yCoord=\"-43\" xCoord=\"43\"/>
                <point yCoord=\"-43\" xCoord=\"74\"/>
            </points>
            <type name=\"int16\"/>
        </model>
        <model tracedRequirements=\"\" description=\"\" id=\"1702982541890_12\" name=\"Input11\" hash=\"47652e68b75f740d7c4228759d31a8f5\" projectFileName=\"\" enable=\"1\" visibility=\"1\">
            <submodels/>
            <type name=\"int16\"/>
            <sourceInstance value=\"1\"/>
            <last value=\"\"/>
            <default value=\"\"/>
            <value value=\"0\"/>
        </model>
        <model tracedRequirements=\"\" description=\"\" id=\"1702982542944_14\" name=\"Input13\" hash=\"47652e68b75f740d7c4228759d31a8f5\" projectFileName=\"\" enable=\"1\" visibility=\"1\">
            <submodels/>
            <type name=\"int16\"/>
            <sourceInstance value=\"1\"/>
            <last value=\"\"/>
            <default value=\"\"/>
            <value value=\"0\"/>
        </model>
        <model tracedRequirements=\"\" description=\"\" id=\"1702982555602_10\" name=\"Output9\" hash=\"1deb5a48a4655393a18760b265134ef3\" projectFileName=\"\" enable=\"1\" visibility=\"1\">
            <submodels/>
            <type name=\"int16\"/>
            <sourceInstance value=\"1\"/>
            <last value=\"\"/>
            <default value=\"\"/>
        </model>
        <model tracedRequirements=\"\" description=\"\" id=\"1702982556952_12\" name=\"Output11\" hash=\"1deb5a48a4655393a18760b265134ef3\" projectFileName=\"\" enable=\"1\" visibility=\"1\">
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
        <startModel hash=\"1702982541890_12\"/>
        <startModel hash=\"1702982542944_14\"/>
    </startModels>
    <endModels>
        <endModel hash=\"1702982555602_10\"/>
        <endModel hash=\"1702982556952_12\"/>
    </endModels>
    <inputSensors/>
    <outputSensors/>
    <locals/>
    <lookups/>
</model>"

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
</model>" ∷ modelStringThatHasCycle ∷ modelStringThatHasCycle2 ∷ doubleOutput ∷ []
