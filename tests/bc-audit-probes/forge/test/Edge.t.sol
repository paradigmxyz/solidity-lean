// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;
import {Edge} from "../src/Edge.sol";
contract EdgeForgeTest {
    Edge t = new Edge();
    function testNegEven() public view { require(t.negBaseEven() == 4, "negEven"); }
    function testNegOdd() public view { require(t.negBaseOdd() == -8, "negOdd"); }
    function testShlSigned() public view { require(t.shlWrapSigned() == -128, "shlSigned"); }
    function testShlUnsigned() public view { require(t.shlTruncUnsigned() == 254, "shlUnsigned"); }
}
