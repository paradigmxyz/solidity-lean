// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

import {CallPositionConsolidatedHarnessTarget} from "../src/CallPositionConsolidated.sol";

// Real solc-0.8.35 / EVM ground truth for the #147-#151 argument-position call
// hoisting family. Each require pins the value the deployed contract returns.
contract CallPositionConsolidatedForgeTest {
    CallPositionConsolidatedHarnessTarget private target =
        new CallPositionConsolidatedHarnessTarget();

    // #147 — call in a modifier-invocation argument (z = a() = 3).
    function testModifierArg() public {
        require(target.modifierArg() == 3, "setZ(a()) must set z = 3");
    }
    // #147 — nested (a()+1) in a modifier-invocation argument (z = 4).
    function testModifierNestedArg() public {
        require(target.modifierNestedArg() == 4, "setZ(a()+1) must set z = 4");
    }

    // #148 — array-literal element calls [a(), b()] -> 3*10 + 4 = 34.
    function testArrayLit() public {
        require(target.arrayLit() == 34, "[a(), b()] must equal 34");
    }
    // #148 — eval order a() before b() (order trail = 12).
    function testArrayLitOrder() public {
        require(target.arrayLitOrder() == 12, "a() then b() order must be 12");
    }

    // #149 — struct-constructor argument calls S(a(), b()) -> 34.
    function testStructArg() public {
        require(target.structArg() == 34, "S(a(), b()) must equal 34");
    }
    // #149 — eval order a() before b() (order trail = 12).
    function testStructArgOrder() public {
        require(target.structArgOrder() == 12, "a() then b() order must be 12");
    }

    // #150 — call in a `new` dynamic-array length argument (length 3).
    function testNewArrayArg() public {
        require(target.newArrayArg() == 3, "new uint256[](a()) length must be 3");
    }
    // #150 — call nested in a `new bytes` length argument (length 5).
    function testNewBytesArg() public {
        require(target.newBytesArg() == 5, "new bytes(a()+2) length must be 5");
    }
    // #150 — call in a `new` contract-constructor argument (t.v() = 3).
    function testNewContractArg() public {
        require(target.newContractArg() == 3, "new T(a()).v() must equal 3");
    }

    // #151 — call nested in a function-call argument inc(a()+1) = 5.
    function testNestedArg() public {
        require(target.nestedArg() == 5, "inc(a()+1) must equal 5");
    }
    // #151 — call nested inside an index argument inc(arr[a()-1]) = 10.
    function testNestedIndexArg() public {
        require(target.nestedIndexArg() == 10, "inc(arr[a()-1]) must equal 10");
    }

    // Controls — call-free argument positions.
    function testCtrlArray() public {
        require(target.ctrlArray() == 12, "call-free array must equal 12");
    }
    function testCtrlStruct() public {
        require(target.ctrlStruct() == 12, "call-free struct must equal 12");
    }
    function testCtrlNewArray() public {
        require(target.ctrlNewArray() == 4, "call-free new array must equal 4");
    }
}
