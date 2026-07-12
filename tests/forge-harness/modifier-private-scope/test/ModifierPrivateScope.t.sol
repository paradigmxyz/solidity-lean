// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

import {Vault2, ShadowDerived, InternalOwnedTarget} from "../src/ModifierPrivateScope.sol";

/// Non-owner caller: this contract is NOT the vault's deployer.
contract Outsider {
    function tryPause(Vault2 vault) external returns (bool ok, string memory reason) {
        try vault.pause() {
            return (true, "");
        } catch Error(string memory m) {
            return (false, m);
        }
    }

    function depositTo(Vault2 vault, uint256 amt)
        external
        returns (bool ok, string memory reason)
    {
        try vault.deposit(amt) {
            return (true, "");
        } catch Error(string memory m) {
            return (false, m);
        }
    }
}

contract ModifierPrivateScopeForgeTest {
    function testMixinStack() public {
        Vault2 vault = new Vault2();
        Outsider outsider = new Outsider();

        require(vault.owner() == address(this), "owner");

        // Outsider deposits through whenNotPaused+guarded.
        (bool depOk, ) = outsider.depositTo(vault, 42);
        require(depOk, "deposit");
        require(vault.balanceOf(address(outsider)) == 42, "bal");

        // Non-owner pause rejected by onlyOwner reading Ownable2's private _owner.
        (bool pauseOk, string memory reason) = outsider.tryPause(vault);
        require(!pauseOk, "outsider pause must fail");
        require(keccak256(bytes(reason)) == keccak256(bytes("own")), "own reason");

        // Owner pauses; deposit now reverts "paused".
        vault.pause();
        require(vault.isPaused(), "paused flag");
        (bool dep2Ok, string memory reason2) = outsider.depositTo(vault, 1);
        require(!dep2Ok, "deposit while paused must fail");
        require(keccak256(bytes(reason2)) == keccak256(bytes("paused")), "paused reason");
    }

    function testShadowBindsBaseSlot() public {
        ShadowDerived shadow = new ShadowDerived();
        require(shadow.baseX() == 7, "baseX");
        require(shadow.derivedX() == 99, "derivedX");
        shadow.f(); // gate reads BASE _x (7), so this passes
        require(shadow.n() == 1, "n");
    }

    function testInternalVarModifierControl() public {
        InternalOwnedTarget target = new InternalOwnedTarget();
        target.f();
        require(target.n() == 1, "keeper n");
    }
}
