// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;
import "../src/DeleteAgg.sol";
import "../src/TryCatch.sol";
import "../src/ConstImm.sol";
contract ExtraTest {
    function testDelStruct() public {
        DeleteAgg d = new DeleteAgg(); d.setup(); d.delStruct();
        require(d.getSA()==0 && d.getSB()==0 && d.getSArrLen()==0, "delStruct");
    }
    function testDelArrElem() public {
        DeleteAgg d = new DeleteAgg(); d.setup(); d.delArrElem();
        require(d.getXs(0)==10 && d.getXs(1)==0 && d.getXs(2)==30 && d.getXsLen()==3, "delElem");
    }
    function testPopAndMap() public {
        DeleteAgg d = new DeleteAgg(); d.setup(); d.popArr(); d.delMapKey();
        require(d.getXsLen()==2 && d.getM(5)==0, "popmap");
    }
    function testTry() public {
        TryCatch t = new TryCatch();
        require(t.run(0)==42, "r0");
        require(t.run(1)==100, "r1");
        require(t.run(2)==300, "r2");
    }
    function testConst() public {
        ConstImm c = new ConstImm(5);
        require(c.getC2()==22 && c.getI1()==5 && c.getI2()==27, "const");
    }
}
