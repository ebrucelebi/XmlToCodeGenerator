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
</model>" ∷ "<model name=\"logicModel2\" description=\"\" tracedRequirements=\"\" projectFileName=\"ExampleIMODESave.prjx\" id=\"1697362424078_3\" hash=\"a67070cb51e7193b57ee8ad63c72b3f5\">
    <submodels>
        <model name=\"Modulo1\" visibility=\"1\" enable=\"1\" description=\"\" tracedRequirements=\"\" projectFileName=\"\" id=\"1697362424080_2\" hash=\"f8806a128e6f1a8d41cfa9b5f0f38f82\">
            <submodels/>
            <ioDirection value=\"0\"/>
            <center yCoord=\"-91\" xCoord=\"-352\"/>
            <size height=\"40\" width=\"60\"/>
            <inputConnections>
                <inputConnection portOrder=\"0\" connectedTo=\"\"/>
                <inputConnection portOrder=\"1\" connectedTo=\"\"/>
            </inputConnections>
            <outputConnections>
                <outputConnection portOrder=\"0\" connectedTo=\"\"/>
            </outputConnections>
            <conditionConnections/>
            <parameterConnections/>
        </model>
        <model name=\"Multiplication1\" visibility=\"1\" enable=\"1\" description=\"\" tracedRequirements=\"\" projectFileName=\"\" id=\"1697362424081_2\" hash=\"c242c66d2b427ca579e166bcb7d29e13\">
            <submodels/>
            <ioDirection value=\"0\"/>
            <center yCoord=\"-83\" xCoord=\"-197\"/>
            <size height=\"40\" width=\"60\"/>
            <inputConnections>
                <inputConnection portOrder=\"0\" connectedTo=\"\"/>
                <inputConnection portOrder=\"1\" connectedTo=\"\"/>
            </inputConnections>
            <outputConnections>
                <outputConnection portOrder=\"0\" connectedTo=\"\"/>
            </outputConnections>
            <conditionConnections/>
            <parameterConnections/>
        </model>
        <model name=\"NumericCast1\" visibility=\"1\" enable=\"1\" description=\"\" tracedRequirements=\"\" projectFileName=\"\" id=\"1697362424081_2\" hash=\"f3717bffb869f6ff1fcce091f166f965\">
            <submodels/>
            <ioDirection value=\"0\"/>
            <center yCoord=\"-85\" xCoord=\"-68\"/>
            <size height=\"40\" width=\"60\"/>
            <inputConnections>
                <inputConnection portOrder=\"0\" connectedTo=\"\"/>
            </inputConnections>
            <outputConnections>
                <outputConnection portOrder=\"0\" connectedTo=\"\"/>
            </outputConnections>
            <conditionConnections/>
            <parameterConnections/>
            <type name=\"int16\"/>
        </model>
        <model name=\"PolymorphicDivision1\" visibility=\"1\" enable=\"1\" description=\"\" tracedRequirements=\"\" projectFileName=\"\" id=\"1697362424082_2\" hash=\"32d7b1f51ebe3b5ef0526278e223fcc9\">
            <submodels/>
            <ioDirection value=\"0\"/>
            <center yCoord=\"-84\" xCoord=\"59\"/>
            <size height=\"40\" width=\"60\"/>
            <inputConnections>
                <inputConnection portOrder=\"0\" connectedTo=\"\"/>
                <inputConnection portOrder=\"1\" connectedTo=\"\"/>
            </inputConnections>
            <outputConnections>
                <outputConnection portOrder=\"0\" connectedTo=\"\"/>
            </outputConnections>
            <conditionConnections/>
            <parameterConnections/>
        </model>
        <model name=\"Subtraction1\" visibility=\"1\" enable=\"1\" description=\"\" tracedRequirements=\"\" projectFileName=\"\" id=\"1697362424082_2\" hash=\"8738acafef8eef7ddb3f91485d3ef88a\">
            <submodels/>
            <ioDirection value=\"0\"/>
            <center yCoord=\"-91\" xCoord=\"191\"/>
            <size height=\"40\" width=\"60\"/>
            <inputConnections>
                <inputConnection portOrder=\"0\" connectedTo=\"\"/>
                <inputConnection portOrder=\"1\" connectedTo=\"\"/>
            </inputConnections>
            <outputConnections>
                <outputConnection portOrder=\"0\" connectedTo=\"\"/>
            </outputConnections>
            <conditionConnections/>
            <parameterConnections/>
        </model>
        <model name=\"UnaryMinus1\" visibility=\"1\" enable=\"1\" description=\"\" tracedRequirements=\"\" projectFileName=\"\" id=\"1697362424083_2\" hash=\"b69fd2eb52ec5bbe329447a438dd969a\">
            <submodels/>
            <ioDirection value=\"0\"/>
            <center yCoord=\"-93\" xCoord=\"312\"/>
            <size height=\"40\" width=\"60\"/>
            <inputConnections>
                <inputConnection portOrder=\"0\" connectedTo=\"\"/>
            </inputConnections>
            <outputConnections>
                <outputConnection portOrder=\"0\" connectedTo=\"\"/>
            </outputConnections>
            <conditionConnections/>
            <parameterConnections/>
        </model>
        <model name=\"LogicalAnd1\" visibility=\"1\" enable=\"1\" description=\"\" tracedRequirements=\"\" projectFileName=\"\" id=\"1697362424083_2\" hash=\"bda26cfe60688578d081dd59071212cc\">
            <submodels/>
            <ioDirection value=\"0\"/>
            <center yCoord=\"3\" xCoord=\"-353\"/>
            <size height=\"40\" width=\"60\"/>
            <inputConnections>
                <inputConnection portOrder=\"0\" connectedTo=\"\"/>
                <inputConnection portOrder=\"1\" connectedTo=\"\"/>
            </inputConnections>
            <outputConnections>
                <outputConnection portOrder=\"0\" connectedTo=\"\"/>
            </outputConnections>
            <conditionConnections/>
            <parameterConnections/>
        </model>
        <model name=\"LogicalNor1\" visibility=\"1\" enable=\"1\" description=\"\" tracedRequirements=\"\" projectFileName=\"\" id=\"1697362424083_2\" hash=\"1bec680337697dc8b16c30e08df84a05\">
            <submodels/>
            <ioDirection value=\"0\"/>
            <center yCoord=\"5\" xCoord=\"-213\"/>
            <size height=\"40\" width=\"60\"/>
            <inputConnections>
                <inputConnection portOrder=\"0\" connectedTo=\"\"/>
                <inputConnection portOrder=\"1\" connectedTo=\"\"/>
            </inputConnections>
            <outputConnections>
                <outputConnection portOrder=\"0\" connectedTo=\"\"/>
            </outputConnections>
            <conditionConnections/>
            <parameterConnections/>
        </model>
        <model name=\"LogicalNot1\" visibility=\"1\" enable=\"1\" description=\"\" tracedRequirements=\"\" projectFileName=\"\" id=\"1697362424084_2\" hash=\"5be489a447538f2bf9867665203e0561\">
            <submodels/>
            <ioDirection value=\"0\"/>
            <center yCoord=\"-4\" xCoord=\"-96\"/>
            <size height=\"40\" width=\"60\"/>
            <inputConnections>
                <inputConnection portOrder=\"0\" connectedTo=\"\"/>
            </inputConnections>
            <outputConnections>
                <outputConnection portOrder=\"0\" connectedTo=\"\"/>
            </outputConnections>
            <conditionConnections/>
            <parameterConnections/>
        </model>
        <model name=\"LogicalOr1\" visibility=\"1\" enable=\"1\" description=\"\" tracedRequirements=\"\" projectFileName=\"\" id=\"1697362424084_2\" hash=\"9c5febda3a36f236a93fdf532df6c5bf\">
            <submodels/>
            <ioDirection value=\"0\"/>
            <center yCoord=\"11\" xCoord=\"5\"/>
            <size height=\"40\" width=\"60\"/>
            <inputConnections>
                <inputConnection portOrder=\"0\" connectedTo=\"\"/>
                <inputConnection portOrder=\"1\" connectedTo=\"\"/>
            </inputConnections>
            <outputConnections>
                <outputConnection portOrder=\"0\" connectedTo=\"\"/>
            </outputConnections>
            <conditionConnections/>
            <parameterConnections/>
        </model>
        <model name=\"LogicalSharp1\" visibility=\"1\" enable=\"1\" description=\"\" tracedRequirements=\"\" projectFileName=\"\" id=\"1697362424085_2\" hash=\"3c5ca129c2ad6f45890b03d9ea594927\">
            <submodels/>
            <ioDirection value=\"0\"/>
            <center yCoord=\"-6\" xCoord=\"128\"/>
            <size height=\"40\" width=\"60\"/>
            <inputConnections>
                <inputConnection portOrder=\"0\" connectedTo=\"\"/>
                <inputConnection portOrder=\"1\" connectedTo=\"\"/>
            </inputConnections>
            <outputConnections>
                <outputConnection portOrder=\"0\" connectedTo=\"\"/>
            </outputConnections>
            <conditionConnections/>
            <parameterConnections/>
        </model>
        <model name=\"LogicalXor1\" visibility=\"1\" enable=\"1\" description=\"\" tracedRequirements=\"\" projectFileName=\"\" id=\"1697362424085_2\" hash=\"5f857ecd847e60cf0b94eb8dfe61555e\">
            <submodels/>
            <ioDirection value=\"0\"/>
            <center yCoord=\"-3\" xCoord=\"272\"/>
            <size height=\"40\" width=\"60\"/>
            <inputConnections>
                <inputConnection portOrder=\"0\" connectedTo=\"\"/>
                <inputConnection portOrder=\"1\" connectedTo=\"\"/>
            </inputConnections>
            <outputConnections>
                <outputConnection portOrder=\"0\" connectedTo=\"\"/>
            </outputConnections>
            <conditionConnections/>
            <parameterConnections/>
        </model>
        <model name=\"BitwiseAnd1\" visibility=\"1\" enable=\"1\" description=\"\" tracedRequirements=\"\" projectFileName=\"\" id=\"1697362424085_2\" hash=\"c9282e847e784046b17a01772be488c2\">
            <submodels/>
            <ioDirection value=\"0\"/>
            <center yCoord=\"98\" xCoord=\"-355\"/>
            <size height=\"40\" width=\"60\"/>
            <inputConnections>
                <inputConnection portOrder=\"0\" connectedTo=\"\"/>
                <inputConnection portOrder=\"1\" connectedTo=\"\"/>
            </inputConnections>
            <outputConnections>
                <outputConnection portOrder=\"0\" connectedTo=\"\"/>
            </outputConnections>
            <conditionConnections/>
            <parameterConnections/>
        </model>
        <model name=\"BitwiseNot1\" visibility=\"1\" enable=\"1\" description=\"\" tracedRequirements=\"\" projectFileName=\"\" id=\"1697362424086_2\" hash=\"bbc0c49eb5b7d5bee5435fc245c46c8d\">
            <submodels/>
            <ioDirection value=\"0\"/>
            <center yCoord=\"106\" xCoord=\"-234\"/>
            <size height=\"40\" width=\"60\"/>
            <inputConnections>
                <inputConnection portOrder=\"0\" connectedTo=\"\"/>
            </inputConnections>
            <outputConnections>
                <outputConnection portOrder=\"0\" connectedTo=\"\"/>
            </outputConnections>
            <conditionConnections/>
            <parameterConnections/>
        </model>
        <model name=\"BitwiseOr1\" visibility=\"1\" enable=\"1\" description=\"\" tracedRequirements=\"\" projectFileName=\"\" id=\"1697362424086_2\" hash=\"c56b0df1c625a2184688ecc1076fbba5\">
            <submodels/>
            <ioDirection value=\"0\"/>
            <center yCoord=\"110\" xCoord=\"-128\"/>
            <size height=\"40\" width=\"60\"/>
            <inputConnections>
                <inputConnection portOrder=\"0\" connectedTo=\"\"/>
                <inputConnection portOrder=\"1\" connectedTo=\"\"/>
            </inputConnections>
            <outputConnections>
                <outputConnection portOrder=\"0\" connectedTo=\"\"/>
            </outputConnections>
            <conditionConnections/>
            <parameterConnections/>
        </model>
        <model name=\"BitwiseXor1\" visibility=\"1\" enable=\"1\" description=\"\" tracedRequirements=\"\" projectFileName=\"\" id=\"1697362424087_2\" hash=\"7b3cbca16789893ffc523eb95d447f40\">
            <submodels/>
            <ioDirection value=\"0\"/>
            <center yCoord=\"105\" xCoord=\"-12\"/>
            <size height=\"40\" width=\"60\"/>
            <inputConnections>
                <inputConnection portOrder=\"0\" connectedTo=\"\"/>
                <inputConnection portOrder=\"1\" connectedTo=\"\"/>
            </inputConnections>
            <outputConnections>
                <outputConnection portOrder=\"0\" connectedTo=\"\"/>
            </outputConnections>
            <conditionConnections/>
            <parameterConnections/>
        </model>
        <model name=\"LeftShift1\" visibility=\"1\" enable=\"1\" description=\"\" tracedRequirements=\"\" projectFileName=\"\" id=\"1697362424087_2\" hash=\"18c8a883eb26ba04ad7f346beae150ea\">
            <submodels/>
            <ioDirection value=\"0\"/>
            <center yCoord=\"110\" xCoord=\"104\"/>
            <size height=\"40\" width=\"60\"/>
            <inputConnections>
                <inputConnection portOrder=\"0\" connectedTo=\"\"/>
                <inputConnection portOrder=\"1\" connectedTo=\"\"/>
            </inputConnections>
            <outputConnections>
                <outputConnection portOrder=\"0\" connectedTo=\"\"/>
            </outputConnections>
            <conditionConnections/>
            <parameterConnections/>
        </model>
        <model name=\"RightShift1\" visibility=\"1\" enable=\"1\" description=\"\" tracedRequirements=\"\" projectFileName=\"\" id=\"1697362424087_2\" hash=\"4ce5e6e4238b68f9ef8eb6cc79a89389\">
            <submodels/>
            <ioDirection value=\"0\"/>
            <center yCoord=\"98\" xCoord=\"239\"/>
            <size height=\"40\" width=\"60\"/>
            <inputConnections>
                <inputConnection portOrder=\"0\" connectedTo=\"\"/>
                <inputConnection portOrder=\"1\" connectedTo=\"\"/>
            </inputConnections>
            <outputConnections>
                <outputConnection portOrder=\"0\" connectedTo=\"\"/>
            </outputConnections>
            <conditionConnections/>
            <parameterConnections/>
        </model>
        <model name=\"Different1\" visibility=\"1\" enable=\"1\" description=\"\" tracedRequirements=\"\" projectFileName=\"\" id=\"1697362424088_2\" hash=\"e25f5536bb430d15c4ecf1c70674d1ae\">
            <submodels/>
            <ioDirection value=\"0\"/>
            <center yCoord=\"180\" xCoord=\"-351\"/>
            <size height=\"40\" width=\"60\"/>
            <inputConnections>
                <inputConnection portOrder=\"0\" connectedTo=\"\"/>
                <inputConnection portOrder=\"1\" connectedTo=\"\"/>
            </inputConnections>
            <outputConnections>
                <outputConnection portOrder=\"0\" connectedTo=\"\"/>
            </outputConnections>
            <conditionConnections/>
            <parameterConnections/>
        </model>
        <model name=\"Equal1\" visibility=\"1\" enable=\"1\" description=\"\" tracedRequirements=\"\" projectFileName=\"\" id=\"1697362424088_2\" hash=\"41f309026b7b989c3ae8dc03f41835d8\">
            <submodels/>
            <ioDirection value=\"0\"/>
            <center yCoord=\"194\" xCoord=\"-246\"/>
            <size height=\"40\" width=\"60\"/>
            <inputConnections>
                <inputConnection portOrder=\"0\" connectedTo=\"\"/>
                <inputConnection portOrder=\"1\" connectedTo=\"\"/>
            </inputConnections>
            <outputConnections>
                <outputConnection portOrder=\"0\" connectedTo=\"\"/>
            </outputConnections>
            <conditionConnections/>
            <parameterConnections/>
        </model>
        <model name=\"GreaterThanEqual1\" visibility=\"1\" enable=\"1\" description=\"\" tracedRequirements=\"\" projectFileName=\"\" id=\"1697362424088_2\" hash=\"28ea640cc30fe446dd8f983de1e9a608\">
            <submodels/>
            <ioDirection value=\"0\"/>
            <center yCoord=\"196\" xCoord=\"-147\"/>
            <size height=\"40\" width=\"60\"/>
            <inputConnections>
                <inputConnection portOrder=\"0\" connectedTo=\"\"/>
                <inputConnection portOrder=\"1\" connectedTo=\"\"/>
            </inputConnections>
            <outputConnections>
                <outputConnection portOrder=\"0\" connectedTo=\"\"/>
            </outputConnections>
            <conditionConnections/>
            <parameterConnections/>
        </model>
        <model name=\"LessThanEqual1\" visibility=\"1\" enable=\"1\" description=\"\" tracedRequirements=\"\" projectFileName=\"\" id=\"1697362424089_2\" hash=\"e2cdc9d4a7472ccc00f1700972004d71\">
            <submodels/>
            <ioDirection value=\"0\"/>
            <center yCoord=\"197\" xCoord=\"-39\"/>
            <size height=\"40\" width=\"60\"/>
            <inputConnections>
                <inputConnection portOrder=\"0\" connectedTo=\"\"/>
                <inputConnection portOrder=\"1\" connectedTo=\"\"/>
            </inputConnections>
            <outputConnections>
                <outputConnection portOrder=\"0\" connectedTo=\"\"/>
            </outputConnections>
            <conditionConnections/>
            <parameterConnections/>
        </model>
        <model name=\"StrictlyGreaterThan1\" visibility=\"1\" enable=\"1\" description=\"\" tracedRequirements=\"\" projectFileName=\"\" id=\"1697362424089_2\" hash=\"c43404828b6fb52b32bbfe69adde0b63\">
            <submodels/>
            <ioDirection value=\"0\"/>
            <center yCoord=\"191\" xCoord=\"87\"/>
            <size height=\"40\" width=\"60\"/>
            <inputConnections>
                <inputConnection portOrder=\"0\" connectedTo=\"\"/>
                <inputConnection portOrder=\"1\" connectedTo=\"\"/>
            </inputConnections>
            <outputConnections>
                <outputConnection portOrder=\"0\" connectedTo=\"\"/>
            </outputConnections>
            <conditionConnections/>
            <parameterConnections/>
        </model>
        <model name=\"StrictlyLessThan1\" visibility=\"1\" enable=\"1\" description=\"\" tracedRequirements=\"\" projectFileName=\"\" id=\"1697362424090_2\" hash=\"10c8829be556be2c9869269b7d3782c2\">
            <submodels/>
            <ioDirection value=\"0\"/>
            <center yCoord=\"196\" xCoord=\"209\"/>
            <size height=\"40\" width=\"60\"/>
            <inputConnections>
                <inputConnection portOrder=\"0\" connectedTo=\"\"/>
                <inputConnection portOrder=\"1\" connectedTo=\"\"/>
            </inputConnections>
            <outputConnections>
                <outputConnection portOrder=\"0\" connectedTo=\"\"/>
            </outputConnections>
            <conditionConnections/>
            <parameterConnections/>
        </model>
    </submodels>
    <genericTypes/>
    <sizeParameters/>
    <startModels/>
    <endModels/>
    <inputSensors/>
    <outputSensors/>
    <locals/>
    <lookups/>
</model>
" ∷ []
