// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

import {GetterNestedStructHarnessTarget} from "../src/GetterNestedStruct.sol";

contract GetterNestedStructForgeTest {
    GetterNestedStructHarnessTarget private target =
        new GetterNestedStructHarnessTarget();

    // The auto getter returns the nested struct WHOLE: (x, (a, arr)).
    function testGetterReturnsNestedStructWhole() public {
        uint256[] memory arr = new uint256[](3);
        arr[0] = 100;
        arr[1] = 200;
        arr[2] = 300;
        target.set(42, 7, arr);

        (uint256 x, GetterNestedStructHarnessTarget.Inner memory inner) =
            target.o();

        require(x == 42, "x");
        require(inner.a == 7, "inner.a");
        require(inner.arr.length == 3, "inner.arr.length");
        require(inner.arr[0] == 100, "arr[0]");
        require(inner.arr[1] == 200, "arr[1]");
        require(inner.arr[2] == 300, "arr[2]");
    }

    function testGetterDefaultsAreZero() public {
        (uint256 x, GetterNestedStructHarnessTarget.Inner memory inner) =
            target.o();
        require(x == 0, "x0");
        require(inner.a == 0, "a0");
        require(inner.arr.length == 0, "len0");
    }
}
