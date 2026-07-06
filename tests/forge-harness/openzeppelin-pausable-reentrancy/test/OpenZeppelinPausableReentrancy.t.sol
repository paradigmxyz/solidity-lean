// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

import {
    OpenZeppelinPausable,
    OpenZeppelinPausableReentrancyHarness,
    OpenZeppelinReentrancyGuard
} from "../src/OpenZeppelinPausableReentrancy.sol";

contract OpenZeppelinPausableReentrancyForgeTest {
    function _expectString(bytes memory actual, string memory expected)
        private
        pure
    {
        require(
            keccak256(actual) == keccak256(abi.encodeWithSignature(
                "Error(string)",
                expected
            )),
            "revert string"
        );
    }

    function testInitialStateTouchAndPauseCycle() public {
        OpenZeppelinPausableReentrancyHarness target =
            new OpenZeppelinPausableReentrancyHarness();

        require(!target.paused(), "initial paused");
        require(!target.entered(), "initial entered");
        require(target.touch() == 1, "touch");
        require(target.touches() == 1, "stored touch");
        require(!target.entered(), "entered reset");

        target.pause();
        require(target.paused(), "paused");

        try target.touch() returns (uint256) {
            revert("expected paused failure");
        } catch (bytes memory reason) {
            _expectString(reason, "Pausable: paused");
        }
        require(target.touches() == 1, "paused rollback");

        require(target.pausedTouch() == 11, "paused touch");
        target.unpause();
        require(!target.paused(), "unpaused");
        require(target.touch() == 12, "touch after unpause");
    }

    function testPauseAndUnpauseFailuresRollback() public {
        OpenZeppelinPausableReentrancyHarness target =
            new OpenZeppelinPausableReentrancyHarness();

        try target.unpause() {
            revert("expected unpause failure");
        } catch (bytes memory reason) {
            _expectString(reason, "Pausable: not paused");
        }
        require(!target.paused(), "still unpaused");

        target.pause();
        try target.pause() {
            revert("expected pause failure");
        } catch (bytes memory reason) {
            _expectString(reason, "Pausable: paused");
        }
        require(target.paused(), "still paused");
        require(target.touches() == 0, "no touch");
    }

    function testNonReentrantEnteredProbeAndFailureRollback() public {
        OpenZeppelinPausableReentrancyHarness target =
            new OpenZeppelinPausableReentrancyHarness();

        require(target.probeEnteredDuringGuard(), "entered during guard");
        require(target.enteredTouches() == 1, "entered count");
        require(!target.entered(), "entered reset");

        try target.failInsideGuard() {
            revert("expected failure");
        } catch (bytes memory reason) {
            _expectString(reason, "boom");
        }
        require(target.touches() == 0, "failure rollback");
        require(!target.entered(), "failure reset");
    }

    function testNestedNonReentrantCallRevertsAndRollsBack() public {
        OpenZeppelinPausableReentrancyHarness target =
            new OpenZeppelinPausableReentrancyHarness();

        try target.callOtherNonReentrant() returns (uint256) {
            revert("expected reentrant failure");
        } catch (bytes memory reason) {
            _expectString(reason, "ReentrancyGuard: reentrant call");
        }

        require(target.touches() == 0, "nested rollback");
        require(!target.entered(), "nested reset");
    }
}
