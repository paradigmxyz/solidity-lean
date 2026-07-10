// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

import {MsqDerived, MsqDerivedU} from "../src/ModifierStaticQualifier.sol";

contract ModifierStaticQualifierForgeTest {
    // Qualified `MsqBase.m` binds statically to MsqBase's modifier.
    function testQualifiedModifierStaticBind() public {
        MsqDerived d = new MsqDerived();
        require(d.f() == 7, "f returns its body value 7");
        require(d.tag() == 1, "Base.m ran: static bind sets tag to 1");
    }

    // Unqualified `m` stays virtual and runs the most-derived override.
    function testUnqualifiedModifierVirtual() public {
        MsqDerivedU u = new MsqDerivedU();
        require(u.f() == 7, "f returns its body value 7");
        require(u.tag() == 2, "override m ran: virtual lookup sets tag to 2");
    }
}
