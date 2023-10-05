module IMODESaveFile where

open import Data.String

projectXmlString : String
projectXmlString = "
<project name=\"Project1\" id=\"1667757607687_1\">
    <submodels>
        <model path=\"logicModel1.mdlx\" hash=\"\"/>
        <model path=\"logicModel3.mdlx\" hash=\"\"/>
        <model path=\"logicModel5.mdlx\" hash=\"\"/>
    </submodels>
    <types path=\"Types.typx\"/>
    <constants path=\"Constants.constx\"/>
    <interfaces path=\"Interfaces.intrfx\"/>
    <ports path=\"Ports.portx\"/>
    <packages>
        <package path=\"Package8/Package8.pkgx\"/>
    </packages>
    <Refs>
        <Ref path=\"D:/AgdaDenemeler/Project6/Project6.prjx\"/>
    </Refs>
    <configurations>
        <configuration path=\"Project1.confx\"/>
    </configurations>
    <version createdVer=\"0.011.6701\" modifiedVer=\"0.011.6701\"/>
    <requirement reqCounter=\"0\"/>
</project>
"

typesXmlString : String
typesXmlString = "<types>
    <type name=\"Int16\" isTypeTemp=\"0\" definition=\"int16\" comment=\"\"/>
    <type name=\"Type2\" isTypeTemp=\"0\" definition=\"uint8\" comment=\"\"/>
    <type name=\"Type3\" isTypeTemp=\"0\" definition=\"&lt;array&gt;\" comment=\"\">
        <arrayInfo name=\"\" isTypeTemp=\"0\" definition=\"int16\" comment=\"\">
            <dimensions>
                <dimension>6</dimension>
            </dimensions>
        </arrayInfo>
    </type>
    <type name=\"Type4\" isTypeTemp=\"0\" definition=\"&lt;structure&gt;\" comment=\"\">
        <definitionElements>
            <definitionElement name=\"label1\" isTypeTemp=\"0\" definition=\"int64\" comment=\"\"/>
            <definitionElement name=\"label2\" isTypeTemp=\"0\" definition=\"int64\" comment=\"\"/>
        </definitionElements>
    </type>
</types>"

interfacesXmlString : String
interfacesXmlString = "<interfaces>
    <interface name=\"Interface1\" isTypeTemp=\"0\" definition=\"int32\" comment=\"\" IO=\"0\" Flag=\"0\" value=\"0\"/>
</interfaces>
"

constantsXmlString : String
constantsXmlString = "<constants>
    <constant name=\"Constant1\" isTypeTemp=\"0\" definition=\"int32\" comment=\"\" value=\"0\"/>
</constants>
"
