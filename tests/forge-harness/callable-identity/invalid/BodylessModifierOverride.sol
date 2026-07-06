// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

contract ImplementedModifierBase {
    modifier guarded() virtual {
        _;
    }
}

abstract contract BodylessModifierOverride is ImplementedModifierBase {
    modifier guarded() virtual override;
}
