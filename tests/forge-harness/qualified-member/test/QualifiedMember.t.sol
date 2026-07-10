// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

import {QualifiedMemberHarnessTarget, I, L} from "../src/QualifiedMember.sol";

contract QualifiedMemberForgeTest {
    function testQualConstBase() public {
        QualifiedMemberHarnessTarget t = new QualifiedMemberHarnessTarget();
        require(t.qualConstBase() == 7, "qualConstBase");
    }

    function testQualConstLib() public {
        QualifiedMemberHarnessTarget t = new QualifiedMemberHarnessTarget();
        require(t.qualConstLib() == 42, "qualConstLib");
    }

    function testQualEnum() public {
        QualifiedMemberHarnessTarget t = new QualifiedMemberHarnessTarget();
        require(t.qualEnum() == 2, "qualEnum");
    }

    function testQualStateVar() public {
        QualifiedMemberHarnessTarget t = new QualifiedMemberHarnessTarget();
        require(t.qualStateVar() == 8, "qualStateVar");
    }

    function testIfaceErrSel() public {
        QualifiedMemberHarnessTarget t = new QualifiedMemberHarnessTarget();
        require(t.ifaceErrSel() == I.IE.selector, "ifaceErrSel");
        require(t.ifaceErrSel() == bytes4(0x1195c9be), "ifaceErrSel value");
    }

    function testLibFnSel() public {
        QualifiedMemberHarnessTarget t = new QualifiedMemberHarnessTarget();
        require(t.libFnSel() == L.g.selector, "libFnSel");
        require(t.libFnSel() == bytes4(0xe420264a), "libFnSel value");
    }

    function testLibErrSel() public {
        QualifiedMemberHarnessTarget t = new QualifiedMemberHarnessTarget();
        require(t.libErrSel() == L.LE.selector, "libErrSel");
        require(t.libErrSel() == bytes4(0x0e0f8818), "libErrSel value");
    }

    function testDoRevert() public {
        QualifiedMemberHarnessTarget t = new QualifiedMemberHarnessTarget();
        try t.doRevert() {
            revert("expected revert");
        } catch (bytes memory reason) {
            // The revert payload is the library error selector + the argument 9.
            require(
                keccak256(reason) ==
                    keccak256(abi.encodeWithSelector(L.LE.selector, uint256(9))),
                "revert payload"
            );
        }
    }
}
