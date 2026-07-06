// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

interface DuplicateLowLevelCatchTarget {
    function fail() external;
}

contract DuplicateLowLevelCatch {
    function bad(DuplicateLowLevelCatchTarget target) external returns (uint256) {
        try target.fail() {
            return 1;
        } catch {
            return 2;
        } catch (bytes memory raw) {
            return raw.length;
        }
    }
}
