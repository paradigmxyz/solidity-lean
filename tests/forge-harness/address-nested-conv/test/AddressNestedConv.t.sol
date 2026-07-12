// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

import {AddressNestedConvTarget} from "../src/AddressNestedConv.sol";

contract AddressNestedConvForgeTest {
    function testD3() public {
        AddressNestedConvTarget t = new AddressNestedConvTarget();
        require(t.d3() == address(0x1234), "d3");
    }
    function testD4() public {
        AddressNestedConvTarget t = new AddressNestedConvTarget();
        require(t.d4() == address(0x1234), "d4");
    }
    function testP3() public {
        AddressNestedConvTarget t = new AddressNestedConvTarget();
        require(t.p3() == payable(address(0x1234)), "p3");
    }
    function testD2() public {
        AddressNestedConvTarget t = new AddressNestedConvTarget();
        require(t.d2() == address(0x1234), "d2");
    }
    function testH() public {
        AddressNestedConvTarget t = new AddressNestedConvTarget();
        require(t.h() == 7, "h");
    }
}
