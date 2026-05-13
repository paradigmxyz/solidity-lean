// SPDX-License-Identifier: MIT
pragma solidity ^0.8.30;

interface CallGasVm {
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
    function deal(address target, uint256 newBalance) external;
}

contract CallGasParityTest {
    CallGasVm internal constant vm = CallGasVm(address(uint160(uint256(keccak256("hevm cheat code")))));

    address internal constant TARGET = 0x1000000000000000000000000000000000000001;
    address internal constant WORKER = 0x2000000000000000000000000000000000000002;
    uint256 internal constant GAS_LIMIT = 1_000_000;

    function testCallValueZeroRequestedGasGetsStipendParity() public {
        bytes memory code = hex"60205f5f5f60017320000000000000000000000000000000000000025ff160205260405ff3";
        bytes memory accountCode = hex"5a5f5260205ff3";
        runCallGasCase("call-value-zero-requested-gas-stipend", code, accountCode, 1);
    }

    function testCallZeroValueZeroRequestedGasNoStipendParity() public {
        bytes memory code = hex"60205f5f5f5f7320000000000000000000000000000000000000025ff160205260405ff3";
        bytes memory accountCode = hex"5a5f5260205ff3";
        runCallGasCase("call-zero-value-zero-requested-gas-no-stipend", code, accountCode, 0);
    }

    function testCallHighRequestedGasGetsEip150CapParity() public {
        bytes memory code = hex"60205f5f5f5f732000000000000000000000000000000000000002620f4240f160205260405ff3";
        bytes memory accountCode = hex"5a5f5260205ff3";
        runCallGasCase("call-high-requested-gas-eip150-cap", code, accountCode, 0);
    }

    function testCallValueHighRequestedGasGetsEip150CapPlusStipendParity() public {
        bytes memory code = hex"60205f5f5f6001732000000000000000000000000000000000000002620f4240f160205260405ff3";
        bytes memory accountCode = hex"5a5f5260205ff3";
        runCallGasCase("call-value-high-requested-gas-eip150-cap-plus-stipend", code, accountCode, 1);
    }

    function testCallZeroLengthHighOffsetsNoExpansionParity() public {
        bytes32 maxWord = bytes32(type(uint256).max);
        bytes memory code = abi.encodePacked(
            hex"5f7f", maxWord, hex"5f7f", maxWord, hex"5f7320000000000000000000000000000000000000025ff15f5260205ff3"
        );
        bytes memory accountCode = hex"00";
        runCallGasCase("call-zero-length-high-offsets-no-expansion", code, accountCode, 0);
    }

    function testCallLikeZeroLengthHighOffsetsNoExpansionParity() public {
        bytes32 maxWord = bytes32(type(uint256).max);
        bytes memory code = abi.encodePacked(
            hex"5f7f",
            maxWord,
            hex"5f7f",
            maxWord,
            hex"5f7320000000000000000000000000000000000000025ff25f52",
            hex"5f7f",
            maxWord,
            hex"5f7f",
            maxWord,
            hex"7320000000000000000000000000000000000000025ff4602052",
            hex"5f7f",
            maxWord,
            hex"5f7f",
            maxWord,
            hex"7320000000000000000000000000000000000000025ffa60405260605ff3"
        );
        bytes memory accountCode = hex"00";
        runCallGasCase("calllike-zero-length-high-offsets-no-expansion", code, accountCode, 0);
    }

    function testCallZeroRequestedGasMemoryExpansionOogParity() public {
        bytes memory code = hex"602062ffffff5f5f5f7320000000000000000000000000000000000000025ff15f5260205ff3";
        bytes memory accountCode = hex"00";
        runCallGasCaseSkippingGas("call-zero-requested-gas-memory-expansion-oog", code, accountCode, 0);
    }

    function runCallGasCase(string memory name, bytes memory code, bytes memory accountCode, uint256 initialBalance)
        internal
    {
        runCallGasCaseWithGasMode(name, code, accountCode, initialBalance, false);
    }

    function runCallGasCaseSkippingGas(
        string memory name,
        bytes memory code,
        bytes memory accountCode,
        uint256 initialBalance
    ) internal {
        runCallGasCaseWithGasMode(name, code, accountCode, initialBalance, true);
    }

    function runCallGasCaseWithGasMode(
        string memory name,
        bytes memory code,
        bytes memory accountCode,
        uint256 initialBalance,
        bool skipGas
    ) internal {
        address target = installRuntime(code);
        vm.deal(target, initialBalance);
        vm.etch(WORKER, accountCode);

        (bool success, bytes memory output) = target.call{gas: GAS_LIMIT}(hex"");
        CallGasVm.Gas memory gas = vm.lastCallGas();

        string[] memory command = new string[](53 + (skipGas ? 1 : 0));
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
        command[28] = uintToString(initialBalance);
        command[29] = "--expect-balance";
        command[30] = uintToString(target.balance);
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
        command[43] = "--account";
        command[44] = string.concat(addressArg(WORKER), "=", hexString(accountCode));
        command[45] = "--account-balance";
        command[46] = string.concat(addressArg(WORKER), "=0");
        command[47] = "--expect-account-balance";
        command[48] = string.concat(addressArg(WORKER), "=", uintToString(WORKER.balance));
        command[49] = "--expect-account-code";
        command[50] = string.concat(addressArg(WORKER), "=", hexString(accountCode));
        command[51] = "--warm-address";
        command[52] = addressArg(WORKER);
        if (skipGas) {
            command[53] = "--skip-gas";
        }

        vm.ffi(command);
    }

    function installRuntime(bytes memory code) internal returns (address target) {
        target = TARGET;
        vm.etch(target, code);
        require(target.code.length == code.length, "runtime not installed");
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
