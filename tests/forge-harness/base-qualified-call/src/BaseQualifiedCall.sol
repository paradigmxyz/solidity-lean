// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

// Linear base: `BqcBaseA.value()` statically bypasses the derived override,
// while `value()` dispatches to the most-derived implementation.
contract BqcBaseA {
    function value() internal virtual returns (uint256) {
        return 1;
    }
}

contract BqcDerivedB is BqcBaseA {
    function value() internal virtual override returns (uint256) {
        return 2;
    }

    function viaBase() external returns (uint256) {
        return BqcBaseA.value();
    }

    function viaDyn() external returns (uint256) {
        return value();
    }
}

// Diamond: each explicit base call resolves statically to that base's body.
contract BqcDiamondA {
    function g() internal virtual returns (uint256) {
        return 10;
    }
}

contract BqcDiamondB is BqcDiamondA {
    function g() internal virtual override returns (uint256) {
        return 20;
    }
}

contract BqcDiamondC is BqcDiamondA {
    function g() internal virtual override returns (uint256) {
        return 30;
    }
}

contract BqcDiamondD is BqcDiamondB, BqcDiamondC {
    function g() internal virtual override(BqcDiamondB, BqcDiamondC)
        returns (uint256)
    {
        return 40;
    }

    function callA() external returns (uint256) {
        return BqcDiamondA.g();
    }

    function callB() external returns (uint256) {
        return BqcDiamondB.g();
    }

    function callC() external returns (uint256) {
        return BqcDiamondC.g();
    }

    function callDyn() external returns (uint256) {
        return g();
    }
}
