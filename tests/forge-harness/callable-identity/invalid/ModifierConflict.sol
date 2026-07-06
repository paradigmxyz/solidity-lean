// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

abstract contract AbstractModifierBase {
    modifier guarded() virtual;
}

contract ConcreteModifierBase {
    modifier guarded() virtual {
        _;
    }
}

abstract contract ModifierConflict is AbstractModifierBase, ConcreteModifierBase {}
