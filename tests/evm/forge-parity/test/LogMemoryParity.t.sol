// SPDX-License-Identifier: MIT
pragma solidity ^0.8.30;

interface LogMemoryVm {
    struct Log {
        bytes32[] topics;
        bytes data;
        address emitter;
    }

    struct Gas {
        uint64 gasLimit;
        uint64 gasTotalUsed;
        uint64 gasMemoryUsed;
        int64 gasRefunded;
        uint64 gasRemaining;
    }

    function ffi(string[] calldata command) external returns (bytes memory result);
    function lastCallGas() external view returns (Gas memory gas);
    function recordLogs() external;
    function getRecordedLogs() external view returns (Log[] memory logs);
    function etch(address target, bytes calldata newRuntimeBytecode) external;
}

contract LogMemoryParityTest {
    LogMemoryVm internal constant vm = LogMemoryVm(address(uint160(uint256(keccak256("hevm cheat code")))));

    address internal constant TARGET = 0x1000000000000000000000000000000000000001;
    uint256 internal constant GAS_LIMIT = 1_000_000;

    function testLog2MemoryExpansionDataAndTopicsParity() public {
        bytes memory code = hex"60ab61010053602260116040610100a200";
        runCase("log2-memory-expansion-data-topics", code);
    }

    function testLog3MemoryExpansionDataAndTopicsParity() public {
        bytes memory code = hex"60de60805360336022601160206080a300";
        runCase("log3-memory-expansion-data-topics", code);
    }

    function testLog0ZeroLengthHighOffsetNoExpansionParity() public {
        bytes memory code = hex"5f62ffffffa000";
        runCase("log0-zero-length-high-offset-no-expansion", code);
    }

    function testLog0ZeroLengthMaxOffsetNoExpansionParity() public {
        bytes memory code = abi.encodePacked(hex"5f7f", bytes32(type(uint256).max), hex"a000");
        runCase("log0-zero-length-max-offset-no-expansion", code);
    }

    function testLog4ZeroLengthMaxOffsetTopicsNoExpansionParity() public {
        bytes memory code = abi.encodePacked(hex"60446033602260115f7f", bytes32(type(uint256).max), hex"a400");
        runCase("log4-zero-length-max-offset-topics-no-expansion", code);
    }

    function testLog1MemoryExpansionOogNoLogParity() public {
        bytes memory code = hex"602a602062ffffffa100";
        runCaseSkippingGas("log1-memory-expansion-oog-no-log", code);
    }

    function runCase(string memory name, bytes memory code) internal {
        runCaseWithGasPolicy(name, code, false);
    }

    function runCaseSkippingGas(string memory name, bytes memory code) internal {
        runCaseWithGasPolicy(name, code, true);
    }

    function runCaseWithGasPolicy(string memory name, bytes memory code, bool skipGas) internal {
        vm.etch(TARGET, code);
        require(TARGET.code.length == code.length, "runtime not installed");

        vm.recordLogs();
        (bool success, bytes memory output) = TARGET.call{gas: GAS_LIMIT}(hex"");
        LogMemoryVm.Gas memory gas = vm.lastCallGas();
        LogMemoryVm.Log[] memory logs = vm.getRecordedLogs();

        string[] memory command = new string[](43 + (skipGas ? 1 : 0) + 2 * logs.length);
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
        for (uint256 i = 0; i < logs.length; i++) {
            command[cursor++] = "--expect-log";
            command[cursor++] = logSpec(logs[i]);
        }

        vm.ffi(command);
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

    function wordHex(bytes32 value) internal pure returns (string memory) {
        return hexString(abi.encodePacked(value));
    }

    function addressArg(address value) internal pure returns (string memory) {
        return hexString(abi.encodePacked(value));
    }

    function addressWordHex(address value) internal pure returns (string memory) {
        return wordHex(bytes32(uint256(uint160(value))));
    }

    function topicsHex(bytes32[] memory topics) internal pure returns (string memory) {
        if (topics.length == 0) return "";
        string memory out = wordHex(topics[0]);
        for (uint256 i = 1; i < topics.length; i++) {
            out = string.concat(out, ",", wordHex(topics[i]));
        }
        return out;
    }

    function logSpec(LogMemoryVm.Log memory entry) internal pure returns (string memory) {
        return string.concat(addressWordHex(entry.emitter), "|", topicsHex(entry.topics), "|", hexString(entry.data));
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
