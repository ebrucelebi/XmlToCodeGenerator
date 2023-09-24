module IMODESaveFile where

open import Data.String

imodeString : String
imodeString = "
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
