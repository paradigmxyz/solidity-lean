// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;
import "../src/Diamond.sol";
contract DiamondTest {
    function testLog1234() public { require((new D()).getLog() == 1234, "no"); }
    function testLog1324() public { require((new D()).getLog() == 1324, "no"); }
    function testWho2() public { require((new D()).who() == 2, "no"); }
    function testWho3() public { require((new D()).who() == 3, "no"); }
}
