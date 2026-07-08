// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

// G19 pin (docs/solidus-solc-deep-comparison.md): an override may RELAX (narrow)
// state mutability relative to the base — solc accepts view->pure and
// nonpayable->view. The override is runtime-identical to any other function; we
// pin acceptance + the dispatched value.
contract MutabilityRelaxOverrideBase {
    // base: view; overridden as pure below.
    function tag(uint256 x) public view virtual returns (uint256) {
        return x + 1;
    }

    // base: nonpayable; overridden as view below.
    function bump(uint256 x) public virtual returns (uint256) {
        return x + 10;
    }
}

// The harness target IS the derived contract: it relaxes view->pure and
// nonpayable->view. Its public entrypoints call the virtual functions
// internally so dispatch resolves to the mutability-relaxed override bodies.
contract MutabilityRelaxOverrideHarnessTarget is MutabilityRelaxOverrideBase {
    // Relax view -> pure.
    function tag(uint256 x) public pure override returns (uint256) {
        return x + 2;
    }

    // Relax nonpayable -> view.
    function bump(uint256 x) public view override returns (uint256) {
        return x + 20;
    }

    // Internal virtual dispatch reaches the relaxed overrides.
    function runTag(uint256 x) public pure returns (uint256) {
        return tag(x);
    }

    function runBump(uint256 x) public view returns (uint256) {
        return bump(x);
    }
}
