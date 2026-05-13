// SPDX-License-Identifier: MIT
pragma solidity ^0.8.30;

interface LogRollbackVm {
    struct Gas {
        uint64 gasLimit;
        uint64 gasTotalUsed;
        uint64 gasMemoryUsed;
        int64 gasRefunded;
        uint64 gasRemaining;
    }

    function ffi(string[] calldata command) external returns (bytes memory result);
    function lastCallGas() external view returns (Gas memory gas);
    function etch(address target, bytes calldata newRuntimeBytecode) external;
}

contract LogRollbackParityTest {
    LogRollbackVm internal constant vm = LogRollbackVm(address(uint160(uint256(keccak256("hevm cheat code")))));

    address internal constant TARGET = 0x1000000000000000000000000000000000000001;
    address internal constant WORKER = 0x2000000000000000000000000000000000000002;
    uint256 internal constant GAS_LIMIT = 1_000_000;

    function testRootRevertRollsBackLogParity() public {
        bytes memory code = hex"602a5f5fa15f5ffd";
        runCase("root-revert-rolls-back-log", code, address(0), hex"", noLogs(), false);
    }

    function testRootInvalidRollsBackLogParity() public {
        bytes memory code = hex"602a5f5fa1fe";
        runCase("root-invalid-rolls-back-log", code, address(0), hex"", noLogs(), true);
    }

    function testRootMemoryOogRollsBackLogParity() public {
        bytes memory code = hex"602a5f5fa1600162ffffff52";
        runCase("root-memory-oog-rolls-back-log", code, address(0), hex"", noLogs(), true);
    }

    function testSuccessfulChildLogCommitsParity() public {
        bytes memory code = hex"5f5f5f5f5f732000000000000000000000000000000000000002620f4240f100";
        bytes memory workerCode = hex"602a5f5fa100";
        runCase("successful-child-log-commits", code, WORKER, workerCode, oneLog(WORKER, 0x2a), false);
    }

    function testRevertedChildLogRollsBackParity() public {
        bytes memory code = hex"5f5f5f5f5f732000000000000000000000000000000000000002620f4240f100";
        bytes memory workerCode = hex"602a5f5fa15f5ffd";
        runCase("reverted-child-log-rolls-back", code, WORKER, workerCode, noLogs(), false);
    }

    function testInvalidChildLogRollsBackParity() public {
        bytes memory code = hex"5f5f5f5f5f732000000000000000000000000000000000000002620f4240f100";
        bytes memory workerCode = hex"602a5f5fa1fe";
        runCase("invalid-child-log-rolls-back", code, WORKER, workerCode, noLogs(), true);
    }

    function testMemoryOogChildLogRollsBackParity() public {
        bytes memory code = hex"5f5f5f5f5f732000000000000000000000000000000000000002620f4240f100";
        bytes memory workerCode = hex"602a5f5fa1600162ffffff52";
        runCase("memory-oog-child-log-rolls-back", code, WORKER, workerCode, noLogs(), true);
    }

    function testParentRevertRollsBackSuccessfulChildLogParity() public {
        bytes memory code = hex"5f5f5f5f5f732000000000000000000000000000000000000002620f4240f15f5ffd";
        bytes memory workerCode = hex"602a5f5fa100";
        runCase("parent-revert-rolls-back-successful-child-log", code, WORKER, workerCode, noLogs(), false);
    }

    function testParentInvalidRollsBackSuccessfulChildLogParity() public {
        bytes memory code = hex"5f5f5f5f5f732000000000000000000000000000000000000002620f4240f1fe";
        bytes memory workerCode = hex"602a5f5fa100";
        runCase("parent-invalid-rolls-back-successful-child-log", code, WORKER, workerCode, noLogs(), true);
    }

    function testParentMemoryOogRollsBackSuccessfulChildLogParity() public {
        bytes memory code = hex"5f5f5f5f5f732000000000000000000000000000000000000002620f4240f1600162ffffff52";
        bytes memory workerCode = hex"602a5f5fa100";
        runCase("parent-memory-oog-rolls-back-successful-child-log", code, WORKER, workerCode, noLogs(), true);
    }

    function testParentThenChildLogOrderParity() public {
        bytes memory code = hex"602b5f5fa15f5f5f5f5f732000000000000000000000000000000000000002620f4240f100";
        bytes memory workerCode = hex"602a5f5fa100";
        runCase("parent-then-child-log-order", code, WORKER, workerCode, twoLogs(TARGET, 0x2b, WORKER, 0x2a), false);
    }

    function testChildThenParentLogOrderParity() public {
        bytes memory code = hex"5f5f5f5f5f732000000000000000000000000000000000000002620f4240f1602b5f5fa100";
        bytes memory workerCode = hex"602a5f5fa100";
        runCase("child-then-parent-log-order", code, WORKER, workerCode, twoLogs(WORKER, 0x2a, TARGET, 0x2b), false);
    }

    function runCase(
        string memory name,
        bytes memory code,
        address account,
        bytes memory accountCode,
        string[] memory expectedLogs,
        bool skipGas
    ) internal {
        vm.etch(TARGET, code);
        require(TARGET.code.length == code.length, "runtime not installed");
        bool hasAccount = account != address(0);
        if (hasAccount) {
            vm.etch(account, accountCode);
            require(account.code.length == accountCode.length, "account runtime not installed");
        }

        (bool success, bytes memory output) = TARGET.call{gas: GAS_LIMIT}(hex"");
        LogRollbackVm.Gas memory gas = vm.lastCallGas();

        string[] memory command = new string[](43 + (skipGas ? 1 : 0) + (hasAccount ? 6 : 0) + 2 * expectedLogs.length);
        command[0] = "python3";
        command[1] = "../../bin/evm_parity.py";
        command[2] = "check";
        command[3] = "--case";
        command[4] = name;
        command[5] = "--code";
        command[6] = hexString(code);
        command[7] = "--calldata";
        command[8] = "0x";
        command[9] = "--gas";
        command[10] = uintToString(gas.gasLimit);
        command[11] = "--success";
        command[12] = success ? "1" : "0";
        command[13] = "--output";
        command[14] = hexString(output);
        command[15] = "--gas-used";
        command[16] = uintToString(gas.gasTotalUsed);
        command[17] = "--gas-remaining";
        command[18] = uintToString(gas.gasRemaining);
        command[19] = "--gas-refunded";
        command[20] = intToString(gas.gasRefunded);
        command[21] = "--caller";
        command[22] = addressArg(address(this));
        command[23] = "--origin";
        command[24] = addressArg(tx.origin);
        command[25] = "--callvalue";
        command[26] = "0";
        command[27] = "--balance";
        command[28] = "0";
        command[29] = "--expect-balance";
        command[30] = uintToString(TARGET.balance);
        command[31] = "--coinbase";
        command[32] = addressArg(block.coinbase);
        command[33] = "--timestamp";
        command[34] = uintToString(block.timestamp);
        command[35] = "--number";
        command[36] = uintToString(block.number);
        command[37] = "--block-gas-limit";
        command[38] = uintToString(block.gaslimit);
        command[39] = "--basefee";
        command[40] = uintToString(block.basefee);
        command[41] = "--chainid";
        command[42] = uintToString(block.chainid);

        uint256 cursor = 43;
        if (skipGas) {
            command[cursor++] = "--skip-gas";
        }
        if (hasAccount) {
            command[cursor++] = "--account";
            command[cursor++] = string.concat(addressArg(account), "=", hexString(accountCode));
            command[cursor++] = "--warm-address";
            command[cursor++] = addressArg(account);
            command[cursor++] = "--expect-account-code";
            command[cursor++] = string.concat(addressArg(account), "=", hexString(accountCode));
        }
        for (uint256 i = 0; i < expectedLogs.length; i++) {
            command[cursor++] = "--expect-log";
            command[cursor++] = expectedLogs[i];
        }

        vm.ffi(command);
    }

    function noLogs() internal pure returns (string[] memory logs) {
        logs = new string[](0);
    }

    function oneLog(address firstEmitter, uint256 firstTopic) internal pure returns (string[] memory logs) {
        logs = new string[](1);
        logs[0] = log1Spec(firstEmitter, firstTopic);
    }

    function twoLogs(address firstEmitter, uint256 firstTopic, address secondEmitter, uint256 secondTopic)
        internal
        pure
        returns (string[] memory logs)
    {
        logs = new string[](2);
        logs[0] = log1Spec(firstEmitter, firstTopic);
        logs[1] = log1Spec(secondEmitter, secondTopic);
    }

    function log1Spec(address emitter, uint256 topic) internal pure returns (string memory) {
        return string.concat(addressWordHex(emitter), "|", wordHex(bytes32(topic)), "|0x");
    }

    function hexString(bytes memory data) internal pure returns (string memory) {
        bytes memory alphabet = "0123456789abcdef";
        bytes memory out = new bytes(2 + data.length * 2);
        out[0] = "0";
        out[1] = "x";
        for (uint256 i = 0; i < data.length; i++) {
            out[2 + i * 2] = alphabet[uint8(data[i]) >> 4];
            out[3 + i * 2] = alphabet[uint8(data[i]) & 0x0f];
        }
        return string(out);
    }

    function addressArg(address value) internal pure returns (string memory) {
        return hexString(abi.encodePacked(value));
    }

    function addressWordHex(address value) internal pure returns (string memory) {
        return wordHex(bytes32(uint256(uint160(value))));
    }

    function wordHex(bytes32 value) internal pure returns (string memory) {
        return hexString(abi.encodePacked(value));
    }

    function uintToString(uint256 value) internal pure returns (string memory) {
        if (value == 0) return "0";
        uint256 temp = value;
        uint256 digits;
        while (temp != 0) {
            digits++;
            temp /= 10;
        }
        bytes memory buffer = new bytes(digits);
        while (value != 0) {
            digits -= 1;
            buffer[digits] = bytes1(uint8(48 + uint256(value % 10)));
            value /= 10;
        }
        return string(buffer);
    }

    function intToString(int256 value) internal pure returns (string memory) {
        if (value >= 0) return uintToString(uint256(value));
        return string.concat("-", uintToString(uint256(-value)));
    }
}
