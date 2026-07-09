// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

/// try/catch clause dispatch by revert KIND (gaps CB1 + A2).
///
/// solc's `tryDecodeErrorMessage` only treats revert data as `Error(string)`
/// when it is at least 0x44 (68) bytes AND decodes as a standard ABI string; a
/// 36-byte `Error`-selector‖zeros payload is NOT an `Error(string)` and routes
/// to the `catch (bytes …)` clause (CB1). Dispatch is by kind (Error / Panic /
/// low-level), not source-order first-match: a revert whose kind has no typed
/// clause falls through to the byte / catch-all clause (A2).
interface IReverter {
    function boom() external;
}

contract CatchDispatch {
    /// Full dispatch surface: Error, Panic, and the byte catch-all.
    /// tag: 1 = success, 2 = Error, 3 = Panic, 4 = bytes/catch-all.
    function route(address t)
        external
        returns (uint256 tag, string memory reason, uint256 len)
    {
        try IReverter(t).boom() {
            tag = 1;
        } catch Error(string memory r) {
            tag = 2;
            reason = r;
        } catch Panic(uint256) {
            tag = 3;
        } catch (bytes memory raw) {
            tag = 4;
            len = raw.length;
        }
    }

    /// No Panic clause: a Panic revert has no typed clause, so it must fall
    /// through to `catch (bytes …)` (kind-based dispatch, A2).
    function routeNoPanic(address t)
        external
        returns (uint256 tag, uint256 len)
    {
        try IReverter(t).boom() {
            tag = 1;
        } catch Error(string memory) {
            tag = 2;
        } catch (bytes memory raw) {
            tag = 4;
            len = raw.length;
        }
    }
}
