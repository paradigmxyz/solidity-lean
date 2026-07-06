// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

type FreeId is uint256;

struct FreePair {
    uint256 left;
    uint256 right;
}

enum FreeChoice {
    A,
    B
}

error FreeBad(uint256 value);

event FreeHit(uint256 indexed value);
event FreeFunctionValue(function (uint256) external fn);

function freeDouble(uint256 x) pure returns (uint256) {
    return x * 2;
}

uint256 constant FREE_CONST = 7;

library SourceDeclarationsLib {
    function inc(uint256 x) internal pure returns (uint256) {
        return x + 1;
    }
}

abstract contract AbstractStorageConstructor {
    struct ConstructorSlot {
        uint256 value;
    }

    uint256 internal observed;

    constructor(ConstructorSlot storage slot) {
        observed = slot.value;
    }
}

contract PublicConstructorVisibility {
    uint256 public value;

    constructor() public {
        value = 1;
    }
}

abstract contract AbstractInternalConstructorVisibility {
    constructor() internal {}
}

contract FallbackOverrideBase {
    fallback() external virtual {}
}

contract FallbackOverrideDerived is FallbackOverrideBase {
    fallback() external override {}
}

contract ReceiveOverrideBase {
    receive() external payable virtual {}
}

contract ReceiveOverrideDerived is ReceiveOverrideBase {
    receive() external payable override {}
}

contract EventStaticAccepted {
    event ThreeIndexed(uint256 indexed a, uint256 indexed b, uint256 indexed c);
    event AnonymousFourIndexed(
        uint256 indexed a,
        uint256 indexed b,
        uint256 indexed c,
        uint256 indexed d
    ) anonymous;
    event ExternalFunction(function (uint256) external fn);
}

contract PrivateShadowBase {
    uint256 private value;

    function setBase(uint256 input) public {
        value = input;
    }

    function readBase() public view returns (uint256) {
        return value;
    }
}

contract PrivateShadowDerived is PrivateShadowBase {
    uint256 private value;

    function setDerived(uint256 input) public {
        value = input;
    }

    function readDerived() public view returns (uint256) {
        return value;
    }

    function runPrivateShadow(uint256 baseValue, uint256 derivedValue)
        external
        returns (uint256, uint256, uint256)
    {
        setBase(baseValue);
        setDerived(derivedValue);
        return (readBase(), readDerived(), value);
    }
}

contract PrivateShadowConstructorBase {
    uint256 private value = 2;

    constructor(uint256 baseInput) {
        value += baseInput;
    }

    function readBaseConstructed() public view returns (uint256) {
        return value;
    }
}

contract PrivateShadowConstructorDerived is PrivateShadowConstructorBase {
    uint256 private value = 11;

    constructor(uint256 baseInput, uint256 derivedInput)
        PrivateShadowConstructorBase(baseInput)
    {
        value += derivedInput;
    }

    function readDerivedConstructed() public view returns (uint256) {
        return value;
    }

    function readConstructed()
        external
        view
        returns (uint256, uint256, uint256)
    {
        return (readBaseConstructed(), readDerivedConstructed(), value);
    }
}

contract SourceDeclarationsHarnessTarget {
    type LocalId is uint256;

    struct LocalPair {
        uint256 a;
        uint256 b;
    }

    enum LocalChoice {
        X,
        Y
    }

    using SourceDeclarationsLib for uint256;

    LocalPair public pair;
    FreePair public freePair;
    LocalChoice public choice;
    FreeChoice public freeChoice;
    uint256[2] private fixedValues;

    function run(uint256 x) external returns (uint256) {
        pair = LocalPair({a: x, b: x + 1});
        freePair = FreePair(x + 2, x + 3);
        choice = LocalChoice.Y;
        freeChoice = FreeChoice.B;
        fixedValues[0] = x;
        fixedValues[1] = x + 10;
        emit FreeHit(x);
        return x.inc() + freeDouble(FREE_CONST);
    }

    function fixedSum() external view returns (uint256) {
        return fixedValues[0] + fixedValues[1];
    }

    function nestedShadow(uint256 input) external pure returns (uint256) {
        uint256 value = input;
        {
            uint256 value = input + 1;
            value;
        }
        return value;
    }
}
