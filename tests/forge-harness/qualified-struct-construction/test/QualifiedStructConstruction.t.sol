// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

import {QualifiedStructConstructionHarnessTarget} from "../src/QualifiedStructConstruction.sol";

contract QualifiedStructConstructionForgeTest {
    function testLibPositional() public {
        QualifiedStructConstructionHarnessTarget t = new QualifiedStructConstructionHarnessTarget();
        require(t.libPositional() == 3, "libPositional");
    }

    function testLibNamed() public {
        QualifiedStructConstructionHarnessTarget t = new QualifiedStructConstructionHarnessTarget();
        require(t.libNamed() == 10020, "libNamed");
    }

    function testContractPositional() public {
        QualifiedStructConstructionHarnessTarget t = new QualifiedStructConstructionHarnessTarget();
        require(t.contractPositional() == 9, "contractPositional");
    }

    function testContractNamed() public {
        QualifiedStructConstructionHarnessTarget t = new QualifiedStructConstructionHarnessTarget();
        require(t.contractNamed() == 100200, "contractNamed");
    }
}
