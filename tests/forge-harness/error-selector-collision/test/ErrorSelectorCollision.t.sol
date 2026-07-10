// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

import {A, B, Derived, UsesFree, Lib} from "../src/ErrorSelectorCollision.sol";

contract ErrorSelectorCollisionForgeTest {
    A private a = new A();
    B private b = new B();
    Derived private d = new Derived();
    UsesFree private u = new UsesFree();

    function testAResolvesOwnBad() public view {
        require(a.s() == A.Bad.selector, "A const");
        require(a.s() == bytes4(0xa2f43130), "A uint256");
    }

    function testBResolvesOwnBad() public view {
        require(b.s() == B.Bad.selector, "B const");
        require(b.s() == bytes4(0x830c4ac2), "B address");
        // Each sibling resolves its OWN Bad — no cross-poisoning.
        require(a.s() != b.s(), "A vs B distinct");
    }

    function testBQualifiedLibrary() public view {
        require(b.q() == Lib.Bad.selector, "B.q const");
        require(b.q() == bytes4(0x30665c7b), "B.q bytes32");
    }

    function testInheritedError() public view {
        require(d.s() == Base_Bad_selector(), "Derived inherited");
        require(d.s() == bytes4(0xa2f43130), "Derived uint256");
    }

    function testFreeError() public view {
        require(u.s() == bytes4(0x381f6d34), "UsesFree bool");
    }

    function Base_Bad_selector() internal pure returns (bytes4) {
        return bytes4(0xa2f43130);
    }
}
