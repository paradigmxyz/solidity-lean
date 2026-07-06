// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

import "../src/SourceDeclarations.sol";

contract SourceDeclarationsForgeTest {
    function testSourceDeclarationsRunAndGetters() public {
        SourceDeclarationsHarnessTarget target =
            new SourceDeclarationsHarnessTarget();

        require(target.run(5) == 20, "run");

        (uint256 a, uint256 b) = target.pair();
        require(a == 5 && b == 6, "pair");

        (uint256 left, uint256 right) = target.freePair();
        require(left == 7 && right == 8, "freePair");

        require(
            target.choice() ==
                SourceDeclarationsHarnessTarget.LocalChoice.Y,
            "choice"
        );
        require(target.freeChoice() == FreeChoice.B, "freeChoice");
        require(target.fixedSum() == 20, "fixedSum");
        require(target.nestedShadow(9) == 9, "nestedShadow");
    }

    function testPrivateInheritedStateShadowing() public {
        PrivateShadowDerived target = new PrivateShadowDerived();
        (uint256 baseValue, uint256 derivedValue, uint256 directDerived) =
            target.runPrivateShadow(5, 7);

        require(baseValue == 5, "base");
        require(derivedValue == 7, "derived");
        require(directDerived == 7, "direct");
        require(target.readBase() == 5, "readBase");
        require(target.readDerived() == 7, "readDerived");
    }

    function testPrivateInheritedStateShadowingConstructors() public {
        PrivateShadowConstructorDerived target =
            new PrivateShadowConstructorDerived(3, 5);
        (uint256 baseValue, uint256 derivedValue, uint256 directDerived) =
            target.readConstructed();

        require(baseValue == 5, "base");
        require(derivedValue == 16, "derived");
        require(directDerived == 16, "direct");
        require(target.readBaseConstructed() == 5, "readBase");
        require(target.readDerivedConstructed() == 16, "readDerived");
    }
}
