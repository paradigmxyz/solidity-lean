// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

import "../src/TryCatch.sol";

contract TryCatchForgeTest {
    function testTryCatchRoutes() public {
        TryCatchHarnessTarget target = new TryCatchHarnessTarget();
        TryCatchHarnessCaller caller = new TryCatchHarnessCaller();

        require(caller.read(target, 4) == 5, "success");
        require(caller.catchError(target) == 3, "error");
        require(caller.catchPanic(target) == 0x12, "panic");
        require(caller.catchRaw(target) == 36, "raw");
        require(caller.bareCatch(target) == 2, "bare");
    }
}
