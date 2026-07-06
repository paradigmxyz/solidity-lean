// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

import {
    OpenZeppelinOwnable,
    OpenZeppelinOwnableForwarder,
    OpenZeppelinOwnableHarnessTarget
} from "../src/OpenZeppelinOwnable.sol";

contract OpenZeppelinOwnableForgeTest {
    function _expectCustom(bytes memory actual, bytes memory expected)
        private
        pure
    {
        require(keccak256(actual) == keccak256(expected), "custom error");
    }

    function testConstructorOwnerAndGuardedCall() public {
        OpenZeppelinOwnableHarnessTarget target =
            new OpenZeppelinOwnableHarnessTarget(address(this));

        require(target.owner() == address(this), "owner");
        require(target.guardedTouch() == 1, "touch");
        require(target.touches() == 1, "stored");
    }

    function testUnauthorizedCallRevertsAndRollsBack() public {
        OpenZeppelinOwnableHarnessTarget target =
            new OpenZeppelinOwnableHarnessTarget(address(this));
        OpenZeppelinOwnableForwarder attacker =
            new OpenZeppelinOwnableForwarder();

        try attacker.guardedTouch(target) returns (uint256) {
            revert("expected revert");
        } catch (bytes memory reason) {
            _expectCustom(
                reason,
                abi.encodeWithSelector(
                    OpenZeppelinOwnable.OwnableUnauthorizedAccount.selector,
                    address(attacker)
                )
            );
        }

        require(target.touches() == 0, "rolled back");
    }

    function testTransferRenounceAndInvalidOwner() public {
        OpenZeppelinOwnableHarnessTarget target =
            new OpenZeppelinOwnableHarnessTarget(address(this));
        OpenZeppelinOwnableForwarder nextOwner =
            new OpenZeppelinOwnableForwarder();

        target.transferOwnership(address(nextOwner));
        require(target.owner() == address(nextOwner), "new owner");
        require(nextOwner.guardedTouch(target) == 1, "new owner touch");

        try target.guardedTouch() returns (uint256) {
            revert("old owner should fail");
        } catch (bytes memory reason) {
            _expectCustom(
                reason,
                abi.encodeWithSelector(
                    OpenZeppelinOwnable.OwnableUnauthorizedAccount.selector,
                    address(this)
                )
            );
        }

        require(nextOwner.renounce(target) == address(0), "renounced");
        require(target.owner() == address(0), "zero owner");

        try nextOwner.guardedTouch(target) returns (uint256) {
            revert("renounced owner should fail");
        } catch (bytes memory reason) {
            _expectCustom(
                reason,
                abi.encodeWithSelector(
                    OpenZeppelinOwnable.OwnableUnauthorizedAccount.selector,
                    address(nextOwner)
                )
            );
        }
    }

    function testInvalidConstructorOwner() public {
        try new OpenZeppelinOwnableHarnessTarget(address(0)) {
            revert("expected revert");
        } catch (bytes memory reason) {
            _expectCustom(
                reason,
                abi.encodeWithSelector(
                    OpenZeppelinOwnable.OwnableInvalidOwner.selector,
                    address(0)
                )
            );
        }
    }
}
