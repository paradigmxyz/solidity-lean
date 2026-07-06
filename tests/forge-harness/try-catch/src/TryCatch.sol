// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

error TryCatchUnknown(uint256 value);

contract TryCatchHarnessTarget {
    function ok(uint256 x) external pure returns (uint256) {
        return x + 1;
    }

    function failError() external pure {
        require(false, "bad");
    }

    function failPanic() external pure {
        uint256 x;
        x = 1 / x;
    }

    function failRaw() external pure {
        revert TryCatchUnknown(7);
    }
}

contract TryCatchHarnessCaller {
    function read(TryCatchHarnessTarget target, uint256 x)
        external
        returns (uint256)
    {
        try target.ok(x) returns (uint256 y) {
            return y;
        } catch Error(string memory reason) {
            return 3;
        } catch Panic(uint256 code) {
            return code;
        } catch (bytes memory raw) {
            return raw.length;
        }
    }

    function catchError(TryCatchHarnessTarget target)
        external
        returns (uint256)
    {
        try target.failError() {
            return 1;
        } catch Error(string memory reason) {
            return 3;
        } catch {
            return 999;
        }
    }

    function catchPanic(TryCatchHarnessTarget target)
        external
        returns (uint256)
    {
        try target.failPanic() {
            return 1;
        } catch Panic(uint256 code) {
            return code;
        }
    }

    function catchRaw(TryCatchHarnessTarget target)
        external
        returns (uint256)
    {
        try target.failRaw() {
            return 1;
        } catch (bytes memory raw) {
            return raw.length;
        }
    }

    function bareCatch(TryCatchHarnessTarget target)
        external
        returns (uint256)
    {
        try target.failError() {
            return 1;
        } catch {
            return 2;
        }
    }
}
