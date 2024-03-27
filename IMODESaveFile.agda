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
        <model path=\"ifExample.mdlx\" hash=\"\"/>
        <model path=\"ifExample2.mdlx\" hash=\"\"/>
        <model path=\"ifExample3.mdlx\" hash=\"\"/>
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

ifExample : String
ifExample = "<model id=\"1710592227361_5\" tracedRequirements=\"\" hash=\"a67070cb51e7193b57ee8ad63c72b3f5\" name=\"ifExample\" projectFileName=\"ExampleIMODESave.prjx\" description=\"\">
    <submodels>
        <model id=\"1710592239427_15\" tracedRequirements=\"\" hash=\"47652e68b75f740d7c4228759d31a8f5\" name=\"_Copy0Input1\" projectFileName=\"\" visibility=\"1\" enable=\"1\" description=\"\">
            <submodels/>
            <ioDirection value=\"0\"/>
            <center xCoord=\"-336\" yCoord=\"-138\"/>
            <size height=\"40\" width=\"60\"/>
            <inputConnections/>
            <outputConnections>
                <outputConnection portOrder=\"0\" connectedTo=\"1710592252981_21\"/>
            </outputConnections>
            <conditionConnections/>
            <parameterConnections/>
            <copyOf value=\"1710592239485_16\"/>
            <last last=\"0\"/>
            <value value=\"0\"/>
        </model>
        <model id=\"1710592245044_17\" tracedRequirements=\"\" hash=\"47652e68b75f740d7c4228759d31a8f5\" name=\"_Copy0Input2\" projectFileName=\"\" visibility=\"1\" enable=\"1\" description=\"\">
            <submodels/>
            <ioDirection value=\"0\"/>
            <center xCoord=\"-341\" yCoord=\"-46\"/>
            <size height=\"40\" width=\"60\"/>
            <inputConnections/>
            <outputConnections>
                <outputConnection portOrder=\"0\" connectedTo=\"1710592253797_22\"/>
            </outputConnections>
            <conditionConnections/>
            <parameterConnections/>
            <copyOf value=\"1710592245120_18\"/>
            <last last=\"0\"/>
            <value value=\"0\"/>
        </model>
        <model id=\"1710592252194_1\" tracedRequirements=\"\" hash=\"c43404828b6fb52b32bbfe69adde0b63\" name=\"StrictlyGreaterThan1\" projectFileName=\"\" visibility=\"1\" enable=\"1\" description=\"\">
            <submodels/>
            <ioDirection value=\"0\"/>
            <center xCoord=\"-168\" yCoord=\"-86\"/>
            <size height=\"40\" width=\"60\"/>
            <inputConnections>
                <inputConnection portOrder=\"0\" connectedTo=\"1710592252981_21\"/>
                <inputConnection portOrder=\"1\" connectedTo=\"1710592253797_22\"/>
            </inputConnections>
            <outputConnections>
                <outputConnection portOrder=\"0\" connectedTo=\"1710592256880_23\"/>
            </outputConnections>
            <conditionConnections/>
            <parameterConnections/>
        </model>
        <model id=\"1710592252981_21\" tracedRequirements=\"\" hash=\"c2459d3d1ef8a0b20f3e7125bae74582\" name=\"Connect21\" projectFileName=\"\" visibility=\"1\" enable=\"1\" description=\"\">
            <submodels/>
            <startOperation xCoord=\"-306\" yCoord=\"-138\" connectedTo=\"1710592239427_15\"/>
            <endOperation xCoord=\"-198\" yCoord=\"-92.66666666666667\" connectedTo=\"1710592252194_1\"/>
            <points>
                <point xCoord=\"-306\" yCoord=\"-138\"/>
                <point xCoord=\"-218\" yCoord=\"-138\"/>
                <point xCoord=\"-218\" yCoord=\"-92.66666666666667\"/>
                <point xCoord=\"-198\" yCoord=\"-92.66666666666667\"/>
            </points>
            <type name=\"int16\"/>
        </model>
        <model id=\"1710592253797_22\" tracedRequirements=\"\" hash=\"c2459d3d1ef8a0b20f3e7125bae74582\" name=\"Connect22\" projectFileName=\"\" visibility=\"1\" enable=\"1\" description=\"\">
            <submodels/>
            <startOperation xCoord=\"-311\" yCoord=\"-46\" connectedTo=\"1710592245044_17\"/>
            <endOperation xCoord=\"-198\" yCoord=\"-79.33333333333333\" connectedTo=\"1710592252194_1\"/>
            <points>
                <point xCoord=\"-311\" yCoord=\"-46\"/>
                <point xCoord=\"-218\" yCoord=\"-46\"/>
                <point xCoord=\"-218\" yCoord=\"-79.33333333333333\"/>
                <point xCoord=\"-198\" yCoord=\"-79.33333333333333\"/>
            </points>
            <type name=\"int16\"/>
        </model>
        <model id=\"1710592255112_1\" tracedRequirements=\"\" hash=\"4fa6a2c3bb81b810e11c467a111b4a7a\" name=\"If1\" projectFileName=\"\" visibility=\"1\" enable=\"1\" description=\"\">
            <submodels/>
            <ioDirection value=\"0\"/>
            <center xCoord=\"29\" yCoord=\"66\"/>
            <size height=\"98\" width=\"148\"/>
            <inputConnections>
                <inputConnection portOrder=\"0\" connectedTo=\"1710592281009_29\"/>
                <inputConnection portOrder=\"1\" connectedTo=\"1710592275621_26\"/>
            </inputConnections>
            <outputConnections>
                <outputConnection portOrder=\"0\" connectedTo=\"1710592290399_30\"/>
            </outputConnections>
            <conditionConnections>
                <conditionConnection portOrder=\"0\" connectedTo=\"1710592256880_23\"/>
            </conditionConnections>
            <parameterConnections/>
        </model>
        <model id=\"1710592256880_23\" tracedRequirements=\"\" hash=\"c2459d3d1ef8a0b20f3e7125bae74582\" name=\"Connect23\" projectFileName=\"\" visibility=\"1\" enable=\"1\" description=\"\">
            <submodels/>
            <startOperation xCoord=\"-138\" yCoord=\"-86\" connectedTo=\"1710592252194_1\"/>
            <endOperation xCoord=\"29\" yCoord=\"17\" connectedTo=\"1710592255112_1\"/>
            <points>
                <point xCoord=\"-138\" yCoord=\"-86\"/>
                <point xCoord=\"29\" yCoord=\"-86\"/>
                <point xCoord=\"29\" yCoord=\"17\"/>
            </points>
            <type name=\"bool\"/>
        </model>
        <model id=\"1710592265198_19\" tracedRequirements=\"\" hash=\"47652e68b75f740d7c4228759d31a8f5\" name=\"Input1_1\" projectFileName=\"\" visibility=\"1\" enable=\"1\" description=\"\">
            <submodels/>
            <ioDirection value=\"0\"/>
            <center xCoord=\"-458\" yCoord=\"22\"/>
            <size height=\"40\" width=\"60\"/>
            <inputConnections/>
            <outputConnections>
                <outputConnection portOrder=\"0\" connectedTo=\"1710592279296_27\"/>
            </outputConnections>
            <conditionConnections/>
            <parameterConnections/>
            <copyOf value=\"1710592239485_16\"/>
            <last last=\"0\"/>
            <value value=\"0\"/>
        </model>
        <model id=\"1710592266085_20\" tracedRequirements=\"\" hash=\"47652e68b75f740d7c4228759d31a8f5\" name=\"Input2_1\" projectFileName=\"\" visibility=\"1\" enable=\"1\" description=\"\">
            <submodels/>
            <ioDirection value=\"0\"/>
            <center xCoord=\"-455\" yCoord=\"123\"/>
            <size height=\"40\" width=\"60\"/>
            <inputConnections/>
            <outputConnections>
                <outputConnection portOrder=\"0\" connectedTo=\"1710592279930_28\"/>
            </outputConnections>
            <conditionConnections/>
            <parameterConnections/>
            <copyOf value=\"1710592245120_18\"/>
            <last last=\"0\"/>
            <value value=\"0\"/>
        </model>
        <model id=\"1710592268194_6\" tracedRequirements=\"\" hash=\"955ca6d568f93954497d59e165f9fa9b\" name=\"Addition6\" projectFileName=\"\" visibility=\"1\" enable=\"1\" description=\"\">
            <submodels/>
            <ioDirection value=\"0\"/>
            <center xCoord=\"-331\" yCoord=\"213\"/>
            <size height=\"40\" width=\"60\"/>
            <inputConnections>
                <inputConnection portOrder=\"0\" connectedTo=\"1710592273829_24\"/>
                <inputConnection portOrder=\"1\" connectedTo=\"1710592274553_25\"/>
            </inputConnections>
            <outputConnections>
                <outputConnection portOrder=\"0\" connectedTo=\"1710592275621_26\"/>
            </outputConnections>
            <conditionConnections/>
            <parameterConnections/>
        </model>
        <model id=\"1710592272301_21\" tracedRequirements=\"\" hash=\"47652e68b75f740d7c4228759d31a8f5\" name=\"Input1_1\" projectFileName=\"\" visibility=\"1\" enable=\"1\" description=\"\">
            <submodels/>
            <ioDirection value=\"0\"/>
            <center xCoord=\"-470\" yCoord=\"186\"/>
            <size height=\"40\" width=\"60\"/>
            <inputConnections/>
            <outputConnections>
                <outputConnection portOrder=\"0\" connectedTo=\"1710592273829_24\"/>
            </outputConnections>
            <conditionConnections/>
            <parameterConnections/>
            <copyOf value=\"1710592239485_16\"/>
            <last last=\"0\"/>
            <value value=\"0\"/>
        </model>
        <model id=\"1710592273211_22\" tracedRequirements=\"\" hash=\"47652e68b75f740d7c4228759d31a8f5\" name=\"Input2_1\" projectFileName=\"\" visibility=\"1\" enable=\"1\" description=\"\">
            <submodels/>
            <ioDirection value=\"0\"/>
            <center xCoord=\"-469\" yCoord=\"244\"/>
            <size height=\"40\" width=\"60\"/>
            <inputConnections/>
            <outputConnections>
                <outputConnection portOrder=\"0\" connectedTo=\"1710592274553_25\"/>
            </outputConnections>
            <conditionConnections/>
            <parameterConnections/>
            <copyOf value=\"1710592245120_18\"/>
            <last last=\"0\"/>
            <value value=\"0\"/>
        </model>
        <model id=\"1710592273829_24\" tracedRequirements=\"\" hash=\"c2459d3d1ef8a0b20f3e7125bae74582\" name=\"Connect24\" projectFileName=\"\" visibility=\"1\" enable=\"1\" description=\"\">
            <submodels/>
            <startOperation xCoord=\"-440\" yCoord=\"186\" connectedTo=\"1710592272301_21\"/>
            <endOperation xCoord=\"-361\" yCoord=\"206.33333333333334\" connectedTo=\"1710592268194_6\"/>
            <points>
                <point xCoord=\"-440\" yCoord=\"186\"/>
                <point xCoord=\"-381\" yCoord=\"186\"/>
                <point xCoord=\"-381\" yCoord=\"206.33333333333334\"/>
                <point xCoord=\"-361\" yCoord=\"206.33333333333334\"/>
            </points>
            <type name=\"int16\"/>
        </model>
        <model id=\"1710592274553_25\" tracedRequirements=\"\" hash=\"c2459d3d1ef8a0b20f3e7125bae74582\" name=\"Connect25\" projectFileName=\"\" visibility=\"1\" enable=\"1\" description=\"\">
            <submodels/>
            <startOperation xCoord=\"-439\" yCoord=\"244\" connectedTo=\"1710592273211_22\"/>
            <endOperation xCoord=\"-361\" yCoord=\"219.66666666666666\" connectedTo=\"1710592268194_6\"/>
            <points>
                <point xCoord=\"-439\" yCoord=\"244\"/>
                <point xCoord=\"-381\" yCoord=\"244\"/>
                <point xCoord=\"-381\" yCoord=\"219.66666666666666\"/>
                <point xCoord=\"-361\" yCoord=\"219.66666666666666\"/>
            </points>
            <type name=\"int16\"/>
        </model>
        <model id=\"1710592275621_26\" tracedRequirements=\"\" hash=\"c2459d3d1ef8a0b20f3e7125bae74582\" name=\"Connect26\" projectFileName=\"\" visibility=\"1\" enable=\"1\" description=\"\">
            <submodels/>
            <startOperation xCoord=\"-301\" yCoord=\"213\" connectedTo=\"1710592268194_6\"/>
            <endOperation xCoord=\"-45\" yCoord=\"82.33333333333333\" connectedTo=\"1710592255112_1\"/>
            <points>
                <point xCoord=\"-301\" yCoord=\"213\"/>
                <point xCoord=\"-122\" yCoord=\"213\"/>
                <point xCoord=\"-122\" yCoord=\"82.33333333333333\"/>
                <point xCoord=\"-45\" yCoord=\"82.33333333333333\"/>
            </points>
            <type name=\"int16\"/>
        </model>
        <model id=\"1710592278893_1\" tracedRequirements=\"\" hash=\"8738acafef8eef7ddb3f91485d3ef88a\" name=\"Subtraction1\" projectFileName=\"\" visibility=\"1\" enable=\"1\" description=\"\">
            <submodels/>
            <ioDirection value=\"0\"/>
            <center xCoord=\"-325\" yCoord=\"16\"/>
            <size height=\"40\" width=\"60\"/>
            <inputConnections>
                <inputConnection portOrder=\"0\" connectedTo=\"1710592279296_27\"/>
                <inputConnection portOrder=\"1\" connectedTo=\"1710592279930_28\"/>
            </inputConnections>
            <outputConnections>
                <outputConnection portOrder=\"0\" connectedTo=\"1710592281009_29\"/>
            </outputConnections>
            <conditionConnections/>
            <parameterConnections/>
        </model>
        <model id=\"1710592279296_27\" tracedRequirements=\"\" hash=\"c2459d3d1ef8a0b20f3e7125bae74582\" name=\"Connect27\" projectFileName=\"\" visibility=\"1\" enable=\"1\" description=\"\">
            <submodels/>
            <startOperation xCoord=\"-428\" yCoord=\"22\" connectedTo=\"1710592265198_19\"/>
            <endOperation xCoord=\"-355\" yCoord=\"9.333333333333334\" connectedTo=\"1710592278893_1\"/>
            <points>
                <point xCoord=\"-428\" yCoord=\"22\"/>
                <point xCoord=\"-380\" yCoord=\"22\"/>
                <point xCoord=\"-380\" yCoord=\"9.333333333333334\"/>
                <point xCoord=\"-355\" yCoord=\"9.333333333333334\"/>
            </points>
            <type name=\"int16\"/>
        </model>
        <model id=\"1710592279930_28\" tracedRequirements=\"\" hash=\"c2459d3d1ef8a0b20f3e7125bae74582\" name=\"Connect28\" projectFileName=\"\" visibility=\"1\" enable=\"1\" description=\"\">
            <submodels/>
            <startOperation xCoord=\"-425\" yCoord=\"123\" connectedTo=\"1710592266085_20\"/>
            <endOperation xCoord=\"-355\" yCoord=\"22.666666666666668\" connectedTo=\"1710592278893_1\"/>
            <points>
                <point xCoord=\"-425\" yCoord=\"123\"/>
                <point xCoord=\"-380\" yCoord=\"123\"/>
                <point xCoord=\"-380\" yCoord=\"22.666666666666668\"/>
                <point xCoord=\"-355\" yCoord=\"22.666666666666668\"/>
            </points>
            <type name=\"int16\"/>
        </model>
        <model id=\"1710592281009_29\" tracedRequirements=\"\" hash=\"c2459d3d1ef8a0b20f3e7125bae74582\" name=\"Connect29\" projectFileName=\"\" visibility=\"1\" enable=\"1\" description=\"\">
            <submodels/>
            <startOperation xCoord=\"-295\" yCoord=\"16\" connectedTo=\"1710592278893_1\"/>
            <endOperation xCoord=\"-45\" yCoord=\"49.666666666666664\" connectedTo=\"1710592255112_1\"/>
            <points>
                <point xCoord=\"-295\" yCoord=\"16\"/>
                <point xCoord=\"-125\" yCoord=\"16\"/>
                <point xCoord=\"-125\" yCoord=\"49.666666666666664\"/>
                <point xCoord=\"-45\" yCoord=\"49.666666666666664\"/>
            </points>
            <type name=\"int16\"/>
        </model>
        <model id=\"1710592289927_11\" tracedRequirements=\"\" hash=\"1deb5a48a4655393a18760b265134ef3\" name=\"_Copy0Output\" projectFileName=\"\" visibility=\"1\" enable=\"1\" description=\"\">
            <submodels/>
            <ioDirection value=\"0\"/>
            <center xCoord=\"268\" yCoord=\"48\"/>
            <size height=\"40\" width=\"60\"/>
            <inputConnections>
                <inputConnection portOrder=\"0\" connectedTo=\"1710592290399_30\"/>
            </inputConnections>
            <outputConnections/>
            <conditionConnections/>
            <parameterConnections/>
            <copyOf value=\"1710592289986_12\"/>
            <last last=\"0\"/>
        </model>
        <model id=\"1710592290399_30\" tracedRequirements=\"\" hash=\"c2459d3d1ef8a0b20f3e7125bae74582\" name=\"Connect30\" projectFileName=\"\" visibility=\"1\" enable=\"1\" description=\"\">
            <submodels/>
            <startOperation xCoord=\"103\" yCoord=\"66\" connectedTo=\"1710592255112_1\"/>
            <endOperation xCoord=\"238\" yCoord=\"48\" connectedTo=\"1710592289927_11\"/>
            <points>
                <point xCoord=\"103\" yCoord=\"66\"/>
                <point xCoord=\"218\" yCoord=\"66\"/>
                <point xCoord=\"218\" yCoord=\"48\"/>
                <point xCoord=\"238\" yCoord=\"48\"/>
            </points>
            <type name=\"int16\"/>
        </model>
        <model id=\"1710592239485_16\" tracedRequirements=\"\" hash=\"47652e68b75f740d7c4228759d31a8f5\" name=\"Input1\" projectFileName=\"\" visibility=\"1\" enable=\"1\" description=\"\">
            <submodels/>
            <type name=\"int16\"/>
            <sourceInstance value=\"1\"/>
            <last value=\"\"/>
            <default value=\"\"/>
            <value value=\"0\"/>
        </model>
        <model id=\"1710592245120_18\" tracedRequirements=\"\" hash=\"47652e68b75f740d7c4228759d31a8f5\" name=\"Input2\" projectFileName=\"\" visibility=\"1\" enable=\"1\" description=\"\">
            <submodels/>
            <type name=\"int16\"/>
            <sourceInstance value=\"1\"/>
            <last value=\"\"/>
            <default value=\"\"/>
            <value value=\"0\"/>
        </model>
        <model id=\"1710592289986_12\" tracedRequirements=\"\" hash=\"1deb5a48a4655393a18760b265134ef3\" name=\"Output\" projectFileName=\"\" visibility=\"1\" enable=\"1\" description=\"\">
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
        <startModel hash=\"1710592239485_16\"/>
        <startModel hash=\"1710592245120_18\"/>
    </startModels>
    <endModels>
        <endModel hash=\"1710592289986_12\"/>
    </endModels>
    <inputSensors/>
    <outputSensors/>
    <locals/>
    <lookups/>
</model>"

ifExample2 : String
ifExample2 = "<model projectFileName=\"ExampleIMODESave.prjx\" name=\"ifExample2\" hash=\"a67070cb51e7193b57ee8ad63c72b3f5\" description=\"\" tracedRequirements=\"\" id=\"1711548075517_6\">
    <submodels>
        <model visibility=\"1\" projectFileName=\"\" name=\"If1\" hash=\"4fa6a2c3bb81b810e11c467a111b4a7a\" enable=\"1\" description=\"\" tracedRequirements=\"\" id=\"1711548117930_3\">
            <submodels/>
            <ioDirection value=\"0\"/>
            <center xCoord=\"-140.5\" yCoord=\"-26.5\"/>
            <size height=\"73\" width=\"101\"/>
            <inputConnections>
                <inputConnection portOrder=\"0\" connectedTo=\"1711548158236_46\"/>
                <inputConnection portOrder=\"1\" connectedTo=\"1711548157599_45\"/>
            </inputConnections>
            <outputConnections>
                <outputConnection portOrder=\"0\" connectedTo=\"1711548153726_43\"/>
                <outputConnection portOrder=\"0\" connectedTo=\"1711548227433_56\"/>
            </outputConnections>
            <conditionConnections>
                <conditionConnection portOrder=\"0\" connectedTo=\"1711548123135_41\"/>
            </conditionConnections>
            <parameterConnections/>
        </model>
        <model visibility=\"1\" projectFileName=\"\" name=\"Connect41\" hash=\"c2459d3d1ef8a0b20f3e7125bae74582\" enable=\"1\" description=\"\" tracedRequirements=\"\" id=\"1711548123135_41\">
            <submodels/>
            <startOperation xCoord=\"-277\" connectedTo=\"1711548137457_35\" yCoord=\"-137\"/>
            <endOperation xCoord=\"-140.5\" connectedTo=\"1711548117930_3\" yCoord=\"-63\"/>
            <points>
                <point xCoord=\"-277\" yCoord=\"-137\"/>
                <point xCoord=\"-140.5\" yCoord=\"-137\"/>
                <point xCoord=\"-140.5\" yCoord=\"-63\"/>
            </points>
            <type name=\"bool\"/>
        </model>
        <model visibility=\"1\" projectFileName=\"\" name=\"If2\" hash=\"4fa6a2c3bb81b810e11c467a111b4a7a\" enable=\"1\" description=\"\" tracedRequirements=\"\" id=\"1711548125723_4\">
            <submodels/>
            <ioDirection value=\"0\"/>
            <center xCoord=\"78\" yCoord=\"134.5\"/>
            <size height=\"75\" width=\"102\"/>
            <inputConnections>
                <inputConnection portOrder=\"0\" connectedTo=\"1711548153726_43\"/>
                <inputConnection portOrder=\"1\" connectedTo=\"1711548155675_44\"/>
            </inputConnections>
            <outputConnections>
                <outputConnection portOrder=\"0\" connectedTo=\"1711548225982_55\"/>
            </outputConnections>
            <conditionConnections>
                <conditionConnection portOrder=\"0\" connectedTo=\"1711548152108_42\"/>
            </conditionConnections>
            <parameterConnections/>
        </model>
        <model visibility=\"1\" projectFileName=\"\" name=\"Cond1\" hash=\"47652e68b75f740d7c4228759d31a8f5\" enable=\"1\" description=\"\" tracedRequirements=\"\" id=\"1711548137457_35\">
            <submodels/>
            <ioDirection value=\"0\"/>
            <center xCoord=\"-307\" yCoord=\"-137\"/>
            <size height=\"40\" width=\"60\"/>
            <inputConnections/>
            <outputConnections>
                <outputConnection portOrder=\"0\" connectedTo=\"1711548123135_41\"/>
            </outputConnections>
            <conditionConnections/>
            <parameterConnections/>
            <copyOf value=\"1711548137505_36\"/>
            <last last=\"0\"/>
            <value value=\"0\"/>
        </model>
        <model visibility=\"1\" projectFileName=\"\" name=\"Cond2\" hash=\"47652e68b75f740d7c4228759d31a8f5\" enable=\"1\" description=\"\" tracedRequirements=\"\" id=\"1711548139256_37\">
            <submodels/>
            <ioDirection value=\"0\"/>
            <center xCoord=\"3\" yCoord=\"53\"/>
            <size height=\"40\" width=\"60\"/>
            <inputConnections/>
            <outputConnections>
                <outputConnection portOrder=\"0\" connectedTo=\"1711548152108_42\"/>
            </outputConnections>
            <conditionConnections/>
            <parameterConnections/>
            <copyOf value=\"1711548139329_38\"/>
            <last last=\"0\"/>
            <value value=\"0\"/>
        </model>
        <model visibility=\"1\" projectFileName=\"\" name=\"Input1\" hash=\"47652e68b75f740d7c4228759d31a8f5\" enable=\"1\" description=\"\" tracedRequirements=\"\" id=\"1711548140806_39\">
            <submodels/>
            <ioDirection value=\"0\"/>
            <center xCoord=\"-331\" yCoord=\"-56\"/>
            <size height=\"40\" width=\"60\"/>
            <inputConnections/>
            <outputConnections>
                <outputConnection portOrder=\"0\" connectedTo=\"1711548158236_46\"/>
            </outputConnections>
            <conditionConnections/>
            <parameterConnections/>
            <copyOf value=\"1711548140858_40\"/>
            <last last=\"0\"/>
            <value value=\"0\"/>
        </model>
        <model visibility=\"1\" projectFileName=\"\" name=\"Input2\" hash=\"47652e68b75f740d7c4228759d31a8f5\" enable=\"1\" description=\"\" tracedRequirements=\"\" id=\"1711548142356_41\">
            <submodels/>
            <ioDirection value=\"0\"/>
            <center xCoord=\"-345\" yCoord=\"14\"/>
            <size height=\"40\" width=\"60\"/>
            <inputConnections/>
            <outputConnections>
                <outputConnection portOrder=\"0\" connectedTo=\"1711548157599_45\"/>
            </outputConnections>
            <conditionConnections/>
            <parameterConnections/>
            <copyOf value=\"1711548142405_42\"/>
            <last last=\"0\"/>
            <value value=\"0\"/>
        </model>
        <model visibility=\"1\" projectFileName=\"\" name=\"Input3\" hash=\"47652e68b75f740d7c4228759d31a8f5\" enable=\"1\" description=\"\" tracedRequirements=\"\" id=\"1711548144751_43\">
            <submodels/>
            <ioDirection value=\"0\"/>
            <center xCoord=\"-117\" yCoord=\"152\"/>
            <size height=\"40\" width=\"60\"/>
            <inputConnections/>
            <outputConnections>
                <outputConnection portOrder=\"0\" connectedTo=\"1711548155675_44\"/>
            </outputConnections>
            <conditionConnections/>
            <parameterConnections/>
            <copyOf value=\"1711548144841_44\"/>
            <last last=\"0\"/>
            <value value=\"0\"/>
        </model>
        <model visibility=\"1\" projectFileName=\"\" name=\"Connect42\" hash=\"c2459d3d1ef8a0b20f3e7125bae74582\" enable=\"1\" description=\"\" tracedRequirements=\"\" id=\"1711548152108_42\">
            <submodels/>
            <startOperation xCoord=\"33\" connectedTo=\"1711548139256_37\" yCoord=\"53\"/>
            <endOperation xCoord=\"78\" connectedTo=\"1711548125723_4\" yCoord=\"97\"/>
            <points>
                <point xCoord=\"33\" yCoord=\"53\"/>
                <point xCoord=\"78\" yCoord=\"53\"/>
                <point xCoord=\"78\" yCoord=\"97\"/>
            </points>
            <type name=\"bool\"/>
        </model>
        <model visibility=\"1\" projectFileName=\"\" name=\"Connect43\" hash=\"c2459d3d1ef8a0b20f3e7125bae74582\" enable=\"1\" description=\"\" tracedRequirements=\"\" id=\"1711548153726_43\">
            <submodels/>
            <startOperation xCoord=\"-90\" connectedTo=\"1711548117930_3\" yCoord=\"-26.5\"/>
            <endOperation xCoord=\"27\" connectedTo=\"1711548125723_4\" yCoord=\"122\"/>
            <points>
                <point xCoord=\"-90\" yCoord=\"-26.5\"/>
                <point xCoord=\"-61\" yCoord=\"-26.5\"/>
                <point xCoord=\"-61\" yCoord=\"122\"/>
                <point xCoord=\"27\" yCoord=\"122\"/>
            </points>
            <type name=\"int16\"/>
        </model>
        <model visibility=\"1\" projectFileName=\"\" name=\"Connect44\" hash=\"c2459d3d1ef8a0b20f3e7125bae74582\" enable=\"1\" description=\"\" tracedRequirements=\"\" id=\"1711548155675_44\">
            <submodels/>
            <startOperation xCoord=\"-87\" connectedTo=\"1711548144751_43\" yCoord=\"152\"/>
            <endOperation xCoord=\"27\" connectedTo=\"1711548125723_4\" yCoord=\"147\"/>
            <points>
                <point xCoord=\"-87\" yCoord=\"152\"/>
                <point xCoord=\"7\" yCoord=\"152\"/>
                <point xCoord=\"7\" yCoord=\"147\"/>
                <point xCoord=\"27\" yCoord=\"147\"/>
            </points>
            <type name=\"int16\"/>
        </model>
        <model visibility=\"1\" projectFileName=\"\" name=\"Connect45\" hash=\"c2459d3d1ef8a0b20f3e7125bae74582\" enable=\"1\" description=\"\" tracedRequirements=\"\" id=\"1711548157599_45\">
            <submodels/>
            <startOperation xCoord=\"-315\" connectedTo=\"1711548142356_41\" yCoord=\"14\"/>
            <endOperation xCoord=\"-191\" connectedTo=\"1711548117930_3\" yCoord=\"-14.333333333333336\"/>
            <points>
                <point xCoord=\"-315\" yCoord=\"14\"/>
                <point xCoord=\"-211\" yCoord=\"14\"/>
                <point xCoord=\"-211\" yCoord=\"-14.333333333333336\"/>
                <point xCoord=\"-191\" yCoord=\"-14.333333333333336\"/>
            </points>
            <type name=\"int16\"/>
        </model>
        <model visibility=\"1\" projectFileName=\"\" name=\"Connect46\" hash=\"c2459d3d1ef8a0b20f3e7125bae74582\" enable=\"1\" description=\"\" tracedRequirements=\"\" id=\"1711548158236_46\">
            <submodels/>
            <startOperation xCoord=\"-301\" connectedTo=\"1711548140806_39\" yCoord=\"-56\"/>
            <endOperation xCoord=\"-191\" connectedTo=\"1711548117930_3\" yCoord=\"-38.66666666666667\"/>
            <points>
                <point xCoord=\"-301\" yCoord=\"-56\"/>
                <point xCoord=\"-211\" yCoord=\"-56\"/>
                <point xCoord=\"-211\" yCoord=\"-38.66666666666667\"/>
                <point xCoord=\"-191\" yCoord=\"-38.66666666666667\"/>
            </points>
            <type name=\"int16\"/>
        </model>
        <model visibility=\"1\" projectFileName=\"\" name=\"Output_1\" hash=\"1deb5a48a4655393a18760b265134ef3\" enable=\"1\" description=\"\" tracedRequirements=\"\" id=\"1711548202968_17\">
            <submodels/>
            <ioDirection value=\"0\"/>
            <center xCoord=\"393\" yCoord=\"50\"/>
            <size height=\"40\" width=\"60\"/>
            <inputConnections>
                <inputConnection portOrder=\"0\" connectedTo=\"1711548230844_57\"/>
            </inputConnections>
            <outputConnections/>
            <conditionConnections/>
            <parameterConnections/>
            <copyOf value=\"1711548075521_13\"/>
            <last last=\"0\"/>
        </model>
        <model visibility=\"1\" projectFileName=\"\" name=\"Addition8\" hash=\"955ca6d568f93954497d59e165f9fa9b\" enable=\"1\" description=\"\" tracedRequirements=\"\" id=\"1711548224252_8\">
            <submodels/>
            <ioDirection value=\"0\"/>
            <center xCoord=\"254\" yCoord=\"50\"/>
            <size height=\"40\" width=\"60\"/>
            <inputConnections>
                <inputConnection portOrder=\"0\" connectedTo=\"1711548227433_56\"/>
                <inputConnection portOrder=\"1\" connectedTo=\"1711548225982_55\"/>
            </inputConnections>
            <outputConnections>
                <outputConnection portOrder=\"0\" connectedTo=\"1711548230844_57\"/>
            </outputConnections>
            <conditionConnections/>
            <parameterConnections/>
        </model>
        <model visibility=\"1\" projectFileName=\"\" name=\"Connect55\" hash=\"c2459d3d1ef8a0b20f3e7125bae74582\" enable=\"1\" description=\"\" tracedRequirements=\"\" id=\"1711548225982_55\">
            <submodels/>
            <startOperation xCoord=\"129\" connectedTo=\"1711548125723_4\" yCoord=\"134.5\"/>
            <endOperation xCoord=\"224\" connectedTo=\"1711548224252_8\" yCoord=\"56.66666666666667\"/>
            <points>
                <point xCoord=\"129\" yCoord=\"134.5\"/>
                <point xCoord=\"188\" yCoord=\"134.5\"/>
                <point xCoord=\"188\" yCoord=\"56.66666666666667\"/>
                <point xCoord=\"224\" yCoord=\"56.66666666666667\"/>
            </points>
            <type name=\"int16\"/>
        </model>
        <model visibility=\"1\" projectFileName=\"\" name=\"Connect56\" hash=\"c2459d3d1ef8a0b20f3e7125bae74582\" enable=\"1\" description=\"\" tracedRequirements=\"\" id=\"1711548227433_56\">
            <submodels/>
            <startOperation xCoord=\"-90\" connectedTo=\"1711548117930_3\" yCoord=\"-26.5\"/>
            <endOperation xCoord=\"224\" connectedTo=\"1711548224252_8\" yCoord=\"43.333333333333336\"/>
            <points>
                <point xCoord=\"-90\" yCoord=\"-26.5\"/>
                <point xCoord=\"188\" yCoord=\"-26.5\"/>
                <point xCoord=\"188\" yCoord=\"43.333333333333336\"/>
                <point xCoord=\"224\" yCoord=\"43.333333333333336\"/>
            </points>
            <type name=\"int16\"/>
        </model>
        <model visibility=\"1\" projectFileName=\"\" name=\"Connect57\" hash=\"c2459d3d1ef8a0b20f3e7125bae74582\" enable=\"1\" description=\"\" tracedRequirements=\"\" id=\"1711548230844_57\">
            <submodels/>
            <startOperation xCoord=\"284\" connectedTo=\"1711548224252_8\" yCoord=\"50\"/>
            <endOperation xCoord=\"363\" connectedTo=\"1711548202968_17\" yCoord=\"50\"/>
            <points>
                <point xCoord=\"284\" yCoord=\"50\"/>
                <point xCoord=\"319\" yCoord=\"50\"/>
                <point xCoord=\"319\" yCoord=\"50\"/>
                <point xCoord=\"363\" yCoord=\"50\"/>
            </points>
            <type name=\"int16\"/>
        </model>
        <model visibility=\"1\" projectFileName=\"\" name=\"Cond1\" hash=\"47652e68b75f740d7c4228759d31a8f5\" enable=\"1\" description=\"\" tracedRequirements=\"\" id=\"1711548137505_36\">
            <submodels/>
            <type name=\"bool\"/>
            <sourceInstance value=\"1\"/>
            <last value=\"\"/>
            <default value=\"\"/>
            <value value=\"0\"/>
        </model>
        <model visibility=\"1\" projectFileName=\"\" name=\"Cond2\" hash=\"47652e68b75f740d7c4228759d31a8f5\" enable=\"1\" description=\"\" tracedRequirements=\"\" id=\"1711548139329_38\">
            <submodels/>
            <type name=\"bool\"/>
            <sourceInstance value=\"1\"/>
            <last value=\"\"/>
            <default value=\"\"/>
            <value value=\"0\"/>
        </model>
        <model visibility=\"1\" projectFileName=\"\" name=\"Input1\" hash=\"47652e68b75f740d7c4228759d31a8f5\" enable=\"1\" description=\"\" tracedRequirements=\"\" id=\"1711548140858_40\">
            <submodels/>
            <type name=\"int16\"/>
            <sourceInstance value=\"1\"/>
            <last value=\"\"/>
            <default value=\"\"/>
            <value value=\"0\"/>
        </model>
        <model visibility=\"1\" projectFileName=\"\" name=\"Input2\" hash=\"47652e68b75f740d7c4228759d31a8f5\" enable=\"1\" description=\"\" tracedRequirements=\"\" id=\"1711548142405_42\">
            <submodels/>
            <type name=\"int16\"/>
            <sourceInstance value=\"1\"/>
            <last value=\"\"/>
            <default value=\"\"/>
            <value value=\"0\"/>
        </model>
        <model visibility=\"1\" projectFileName=\"\" name=\"Input3\" hash=\"47652e68b75f740d7c4228759d31a8f5\" enable=\"1\" description=\"\" tracedRequirements=\"\" id=\"1711548144841_44\">
            <submodels/>
            <type name=\"int16\"/>
            <sourceInstance value=\"1\"/>
            <last value=\"\"/>
            <default value=\"\"/>
            <value value=\"0\"/>
        </model>
        <model visibility=\"1\" projectFileName=\"\" name=\"Output\" hash=\"1deb5a48a4655393a18760b265134ef3\" enable=\"1\" description=\"\" tracedRequirements=\"\" id=\"1711548075521_13\">
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
        <startModel hash=\"1711548137505_36\"/>
        <startModel hash=\"1711548139329_38\"/>
        <startModel hash=\"1711548140858_40\"/>
        <startModel hash=\"1711548142405_42\"/>
        <startModel hash=\"1711548144841_44\"/>
    </startModels>
    <endModels>
        <endModel hash=\"1711548075521_13\"/>
    </endModels>
    <inputSensors/>
    <outputSensors/>
    <locals/>
    <lookups/>
</model>"

ifExample3 : String
ifExample3 = "<model projectFileName=\"ExampleIMODESave.prjx\" name=\"ifExample3\" hash=\"a67070cb51e7193b57ee8ad63c72b3f5\" description=\"\" tracedRequirements=\"\" id=\"1711548209593_7\">
    <submodels>
        <model visibility=\"1\" projectFileName=\"\" name=\"If1\" hash=\"4fa6a2c3bb81b810e11c467a111b4a7a\" enable=\"1\" description=\"\" tracedRequirements=\"\" id=\"1711548209596_5\">
            <submodels/>
            <ioDirection value=\"0\"/>
            <center xCoord=\"-140.5\" yCoord=\"-26.5\"/>
            <size height=\"73\" width=\"101\"/>
            <inputConnections>
                <inputConnection portOrder=\"0\" connectedTo=\"1711548209598_53\"/>
                <inputConnection portOrder=\"1\" connectedTo=\"1711548209598_52\"/>
            </inputConnections>
            <outputConnections>
                <outputConnection portOrder=\"0\" connectedTo=\"1711548209598_50\"/>
            </outputConnections>
            <conditionConnections>
                <conditionConnection portOrder=\"0\" connectedTo=\"1711548209596_48\"/>
            </conditionConnections>
            <parameterConnections/>
        </model>
        <model visibility=\"1\" projectFileName=\"\" name=\"Connect41\" hash=\"c2459d3d1ef8a0b20f3e7125bae74582\" enable=\"1\" description=\"\" tracedRequirements=\"\" id=\"1711548209596_48\">
            <submodels/>
            <startOperation xCoord=\"-277\" connectedTo=\"1711548209597_52\" yCoord=\"-137\"/>
            <endOperation xCoord=\"-140.5\" connectedTo=\"1711548209596_5\" yCoord=\"-63\"/>
            <points>
                <point xCoord=\"-277\" yCoord=\"-137\"/>
                <point xCoord=\"-140.5\" yCoord=\"-137\"/>
                <point xCoord=\"-140.5\" yCoord=\"-63\"/>
            </points>
            <type name=\"bool\"/>
        </model>
        <model visibility=\"1\" projectFileName=\"\" name=\"If2\" hash=\"4fa6a2c3bb81b810e11c467a111b4a7a\" enable=\"1\" description=\"\" tracedRequirements=\"\" id=\"1711548209596_6\">
            <submodels/>
            <ioDirection value=\"0\"/>
            <center xCoord=\"-105\" yCoord=\"159.5\"/>
            <size height=\"75\" width=\"102\"/>
            <inputConnections>
                <inputConnection portOrder=\"0\" connectedTo=\"1711548209598_51\"/>
                <inputConnection portOrder=\"1\" connectedTo=\"1711548257535_58\"/>
            </inputConnections>
            <outputConnections>
                <outputConnection portOrder=\"0\" connectedTo=\"1711548265539_59\"/>
            </outputConnections>
            <conditionConnections>
                <conditionConnection portOrder=\"0\" connectedTo=\"1711548209598_49\"/>
            </conditionConnections>
            <parameterConnections/>
        </model>
        <model visibility=\"1\" projectFileName=\"\" name=\"Cond1\" hash=\"47652e68b75f740d7c4228759d31a8f5\" enable=\"1\" description=\"\" tracedRequirements=\"\" id=\"1711548209597_52\">
            <submodels/>
            <ioDirection value=\"0\"/>
            <center xCoord=\"-307\" yCoord=\"-137\"/>
            <size height=\"40\" width=\"60\"/>
            <inputConnections/>
            <outputConnections>
                <outputConnection portOrder=\"0\" connectedTo=\"1711548209596_48\"/>
            </outputConnections>
            <conditionConnections/>
            <parameterConnections/>
            <copyOf value=\"1711548209594_47\"/>
            <last last=\"0\"/>
            <value value=\"0\"/>
        </model>
        <model visibility=\"1\" projectFileName=\"\" name=\"Cond2\" hash=\"47652e68b75f740d7c4228759d31a8f5\" enable=\"1\" description=\"\" tracedRequirements=\"\" id=\"1711548209597_53\">
            <submodels/>
            <ioDirection value=\"0\"/>
            <center xCoord=\"-180\" yCoord=\"78\"/>
            <size height=\"40\" width=\"60\"/>
            <inputConnections/>
            <outputConnections>
                <outputConnection portOrder=\"0\" connectedTo=\"1711548209598_49\"/>
            </outputConnections>
            <conditionConnections/>
            <parameterConnections/>
            <copyOf value=\"1711548209594_48\"/>
            <last last=\"0\"/>
            <value value=\"0\"/>
        </model>
        <model visibility=\"1\" projectFileName=\"\" name=\"Input1\" hash=\"47652e68b75f740d7c4228759d31a8f5\" enable=\"1\" description=\"\" tracedRequirements=\"\" id=\"1711548209597_54\">
            <submodels/>
            <ioDirection value=\"0\"/>
            <center xCoord=\"-331\" yCoord=\"-56\"/>
            <size height=\"40\" width=\"60\"/>
            <inputConnections/>
            <outputConnections>
                <outputConnection portOrder=\"0\" connectedTo=\"1711548209598_53\"/>
            </outputConnections>
            <conditionConnections/>
            <parameterConnections/>
            <copyOf value=\"1711548209595_49\"/>
            <last last=\"0\"/>
            <value value=\"0\"/>
        </model>
        <model visibility=\"1\" projectFileName=\"\" name=\"Input2\" hash=\"47652e68b75f740d7c4228759d31a8f5\" enable=\"1\" description=\"\" tracedRequirements=\"\" id=\"1711548209597_55\">
            <submodels/>
            <ioDirection value=\"0\"/>
            <center xCoord=\"-345\" yCoord=\"14\"/>
            <size height=\"40\" width=\"60\"/>
            <inputConnections/>
            <outputConnections>
                <outputConnection portOrder=\"0\" connectedTo=\"1711548209598_52\"/>
            </outputConnections>
            <conditionConnections/>
            <parameterConnections/>
            <copyOf value=\"1711548209595_50\"/>
            <last last=\"0\"/>
            <value value=\"0\"/>
        </model>
        <model visibility=\"1\" projectFileName=\"\" name=\"Input3\" hash=\"47652e68b75f740d7c4228759d31a8f5\" enable=\"1\" description=\"\" tracedRequirements=\"\" id=\"1711548209598_56\">
            <submodels/>
            <ioDirection value=\"0\"/>
            <center xCoord=\"-319\" yCoord=\"129\"/>
            <size height=\"40\" width=\"60\"/>
            <inputConnections/>
            <outputConnections>
                <outputConnection portOrder=\"0\" connectedTo=\"1711548209598_51\"/>
            </outputConnections>
            <conditionConnections/>
            <parameterConnections/>
            <copyOf value=\"1711548209595_51\"/>
            <last last=\"0\"/>
            <value value=\"0\"/>
        </model>
        <model visibility=\"1\" projectFileName=\"\" name=\"Connect42\" hash=\"c2459d3d1ef8a0b20f3e7125bae74582\" enable=\"1\" description=\"\" tracedRequirements=\"\" id=\"1711548209598_49\">
            <submodels/>
            <startOperation xCoord=\"-150\" connectedTo=\"1711548209597_53\" yCoord=\"78\"/>
            <endOperation xCoord=\"-105\" connectedTo=\"1711548209596_6\" yCoord=\"122\"/>
            <points>
                <point xCoord=\"-150\" yCoord=\"78\"/>
                <point xCoord=\"-105\" yCoord=\"78\"/>
                <point xCoord=\"-105\" yCoord=\"122\"/>
            </points>
            <type name=\"bool\"/>
        </model>
        <model visibility=\"1\" projectFileName=\"\" name=\"Connect43\" hash=\"c2459d3d1ef8a0b20f3e7125bae74582\" enable=\"1\" description=\"\" tracedRequirements=\"\" id=\"1711548209598_50\">
            <submodels/>
            <startOperation xCoord=\"-90\" connectedTo=\"1711548209596_5\" yCoord=\"-26.5\"/>
            <endOperation xCoord=\"78\" connectedTo=\"1711548249118_9\" yCoord=\"53.333333333333336\"/>
            <points>
                <point xCoord=\"-90\" yCoord=\"-26.5\"/>
                <point xCoord=\"-61\" yCoord=\"-26.5\"/>
                <point xCoord=\"-61\" yCoord=\"53.333333333333336\"/>
                <point xCoord=\"78\" yCoord=\"53.333333333333336\"/>
            </points>
            <type name=\"int16\"/>
        </model>
        <model visibility=\"1\" projectFileName=\"\" name=\"Connect44\" hash=\"c2459d3d1ef8a0b20f3e7125bae74582\" enable=\"1\" description=\"\" tracedRequirements=\"\" id=\"1711548209598_51\">
            <submodels/>
            <startOperation xCoord=\"-289\" connectedTo=\"1711548209598_56\" yCoord=\"129\"/>
            <endOperation xCoord=\"-156\" connectedTo=\"1711548209596_6\" yCoord=\"147\"/>
            <points>
                <point xCoord=\"-289\" yCoord=\"129\"/>
                <point xCoord=\"-176\" yCoord=\"129\"/>
                <point xCoord=\"-176\" yCoord=\"147\"/>
                <point xCoord=\"-156\" yCoord=\"147\"/>
            </points>
            <type name=\"int16\"/>
        </model>
        <model visibility=\"1\" projectFileName=\"\" name=\"Connect45\" hash=\"c2459d3d1ef8a0b20f3e7125bae74582\" enable=\"1\" description=\"\" tracedRequirements=\"\" id=\"1711548209598_52\">
            <submodels/>
            <startOperation xCoord=\"-315\" connectedTo=\"1711548209597_55\" yCoord=\"14\"/>
            <endOperation xCoord=\"-191\" connectedTo=\"1711548209596_5\" yCoord=\"-14.333333333333336\"/>
            <points>
                <point xCoord=\"-315\" yCoord=\"14\"/>
                <point xCoord=\"-211\" yCoord=\"14\"/>
                <point xCoord=\"-211\" yCoord=\"-14.333333333333336\"/>
                <point xCoord=\"-191\" yCoord=\"-14.333333333333336\"/>
            </points>
            <type name=\"int16\"/>
        </model>
        <model visibility=\"1\" projectFileName=\"\" name=\"Connect46\" hash=\"c2459d3d1ef8a0b20f3e7125bae74582\" enable=\"1\" description=\"\" tracedRequirements=\"\" id=\"1711548209598_53\">
            <submodels/>
            <startOperation xCoord=\"-301\" connectedTo=\"1711548209597_54\" yCoord=\"-56\"/>
            <endOperation xCoord=\"-191\" connectedTo=\"1711548209596_5\" yCoord=\"-38.66666666666667\"/>
            <points>
                <point xCoord=\"-301\" yCoord=\"-56\"/>
                <point xCoord=\"-211\" yCoord=\"-56\"/>
                <point xCoord=\"-211\" yCoord=\"-38.66666666666667\"/>
                <point xCoord=\"-191\" yCoord=\"-38.66666666666667\"/>
            </points>
            <type name=\"int16\"/>
        </model>
        <model visibility=\"1\" projectFileName=\"\" name=\"Connect47\" hash=\"c2459d3d1ef8a0b20f3e7125bae74582\" enable=\"1\" description=\"\" tracedRequirements=\"\" id=\"1711548209598_54\">
            <submodels/>
            <startOperation xCoord=\"138\" connectedTo=\"1711548249118_9\" yCoord=\"60\"/>
            <endOperation xCoord=\"273\" connectedTo=\"1711548209598_19\" yCoord=\"66\"/>
            <points>
                <point xCoord=\"138\" yCoord=\"60\"/>
                <point xCoord=\"216\" yCoord=\"60\"/>
                <point xCoord=\"216\" yCoord=\"66\"/>
                <point xCoord=\"273\" yCoord=\"66\"/>
            </points>
            <type name=\"int16\"/>
        </model>
        <model visibility=\"1\" projectFileName=\"\" name=\"Output\" hash=\"1deb5a48a4655393a18760b265134ef3\" enable=\"1\" description=\"\" tracedRequirements=\"\" id=\"1711548209598_19\">
            <submodels/>
            <ioDirection value=\"0\"/>
            <center xCoord=\"303\" yCoord=\"66\"/>
            <size height=\"40\" width=\"60\"/>
            <inputConnections>
                <inputConnection portOrder=\"0\" connectedTo=\"1711548209598_54\"/>
            </inputConnections>
            <outputConnections/>
            <conditionConnections/>
            <parameterConnections/>
            <copyOf value=\"1711548209596_18\"/>
            <last last=\"0\"/>
        </model>
        <model visibility=\"1\" projectFileName=\"\" name=\"Addition9\" hash=\"955ca6d568f93954497d59e165f9fa9b\" enable=\"1\" description=\"\" tracedRequirements=\"\" id=\"1711548249118_9\">
            <submodels/>
            <ioDirection value=\"0\"/>
            <center xCoord=\"108\" yCoord=\"60\"/>
            <size height=\"40\" width=\"60\"/>
            <inputConnections>
                <inputConnection portOrder=\"0\" connectedTo=\"1711548209598_50\"/>
                <inputConnection portOrder=\"1\" connectedTo=\"1711548265539_59\"/>
            </inputConnections>
            <outputConnections>
                <outputConnection portOrder=\"0\" connectedTo=\"1711548209598_54\"/>
            </outputConnections>
            <conditionConnections/>
            <parameterConnections/>
        </model>
        <model visibility=\"1\" projectFileName=\"\" name=\"Input4\" hash=\"47652e68b75f740d7c4228759d31a8f5\" enable=\"1\" description=\"\" tracedRequirements=\"\" id=\"1711548253401_57\">
            <submodels/>
            <ioDirection value=\"0\"/>
            <center xCoord=\"-329\" yCoord=\"200\"/>
            <size height=\"40\" width=\"60\"/>
            <inputConnections/>
            <outputConnections>
                <outputConnection portOrder=\"0\" connectedTo=\"1711548257535_58\"/>
            </outputConnections>
            <conditionConnections/>
            <parameterConnections/>
            <copyOf value=\"1711548253444_58\"/>
            <last last=\"0\"/>
            <value value=\"0\"/>
        </model>
        <model visibility=\"1\" projectFileName=\"\" name=\"Connect58\" hash=\"c2459d3d1ef8a0b20f3e7125bae74582\" enable=\"1\" description=\"\" tracedRequirements=\"\" id=\"1711548257535_58\">
            <submodels/>
            <startOperation xCoord=\"-299\" connectedTo=\"1711548253401_57\" yCoord=\"200\"/>
            <endOperation xCoord=\"-156\" connectedTo=\"1711548209596_6\" yCoord=\"172\"/>
            <points>
                <point xCoord=\"-299\" yCoord=\"200\"/>
                <point xCoord=\"-176\" yCoord=\"200\"/>
                <point xCoord=\"-176\" yCoord=\"172\"/>
                <point xCoord=\"-156\" yCoord=\"172\"/>
            </points>
            <type name=\"int16\"/>
        </model>
        <model visibility=\"1\" projectFileName=\"\" name=\"Connect59\" hash=\"c2459d3d1ef8a0b20f3e7125bae74582\" enable=\"1\" description=\"\" tracedRequirements=\"\" id=\"1711548265539_59\">
            <submodels/>
            <startOperation xCoord=\"-54\" connectedTo=\"1711548209596_6\" yCoord=\"159.5\"/>
            <endOperation xCoord=\"78\" connectedTo=\"1711548249118_9\" yCoord=\"66.66666666666667\"/>
            <points>
                <point xCoord=\"-54\" yCoord=\"159.5\"/>
                <point xCoord=\"-34\" yCoord=\"159.5\"/>
                <point xCoord=\"-34\" yCoord=\"66.66666666666667\"/>
                <point xCoord=\"78\" yCoord=\"66.66666666666667\"/>
            </points>
            <type name=\"int16\"/>
        </model>
        <model visibility=\"1\" projectFileName=\"\" name=\"Cond1\" hash=\"47652e68b75f740d7c4228759d31a8f5\" enable=\"1\" description=\"\" tracedRequirements=\"\" id=\"1711548209594_47\">
            <submodels/>
            <type name=\"bool\"/>
            <sourceInstance value=\"1\"/>
            <last value=\"\"/>
            <default value=\"\"/>
            <value value=\"0\"/>
        </model>
        <model visibility=\"1\" projectFileName=\"\" name=\"Cond2\" hash=\"47652e68b75f740d7c4228759d31a8f5\" enable=\"1\" description=\"\" tracedRequirements=\"\" id=\"1711548209594_48\">
            <submodels/>
            <type name=\"bool\"/>
            <sourceInstance value=\"1\"/>
            <last value=\"\"/>
            <default value=\"\"/>
            <value value=\"0\"/>
        </model>
        <model visibility=\"1\" projectFileName=\"\" name=\"Input1\" hash=\"47652e68b75f740d7c4228759d31a8f5\" enable=\"1\" description=\"\" tracedRequirements=\"\" id=\"1711548209595_49\">
            <submodels/>
            <type name=\"int16\"/>
            <sourceInstance value=\"1\"/>
            <last value=\"\"/>
            <default value=\"\"/>
            <value value=\"0\"/>
        </model>
        <model visibility=\"1\" projectFileName=\"\" name=\"Input2\" hash=\"47652e68b75f740d7c4228759d31a8f5\" enable=\"1\" description=\"\" tracedRequirements=\"\" id=\"1711548209595_50\">
            <submodels/>
            <type name=\"int16\"/>
            <sourceInstance value=\"1\"/>
            <last value=\"\"/>
            <default value=\"\"/>
            <value value=\"0\"/>
        </model>
        <model visibility=\"1\" projectFileName=\"\" name=\"Input3\" hash=\"47652e68b75f740d7c4228759d31a8f5\" enable=\"1\" description=\"\" tracedRequirements=\"\" id=\"1711548209595_51\">
            <submodels/>
            <type name=\"int16\"/>
            <sourceInstance value=\"1\"/>
            <last value=\"\"/>
            <default value=\"\"/>
            <value value=\"0\"/>
        </model>
        <model visibility=\"1\" projectFileName=\"\" name=\"Input4\" hash=\"47652e68b75f740d7c4228759d31a8f5\" enable=\"1\" description=\"\" tracedRequirements=\"\" id=\"1711548253444_58\">
            <submodels/>
            <type name=\"int16\"/>
            <sourceInstance value=\"1\"/>
            <last value=\"\"/>
            <default value=\"\"/>
            <value value=\"0\"/>
        </model>
        <model visibility=\"1\" projectFileName=\"\" name=\"Output\" hash=\"1deb5a48a4655393a18760b265134ef3\" enable=\"1\" description=\"\" tracedRequirements=\"\" id=\"1711548209596_18\">
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
        <startModel hash=\"1711548209594_47\"/>
        <startModel hash=\"1711548209594_48\"/>
        <startModel hash=\"1711548209595_49\"/>
        <startModel hash=\"1711548209595_50\"/>
        <startModel hash=\"1711548209595_51\"/>
        <startModel hash=\"1711548253444_58\"/>
    </startModels>
    <endModels>
        <endModel hash=\"1711548209596_18\"/>
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
</model>" ∷ modelStringThatHasCycle ∷ modelStringThatHasCycle2 ∷ doubleOutput ∷ ifExample ∷ ifExample2 ∷ ifExample3 ∷ []
