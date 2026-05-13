// SPDX-License-Identifier: MIT
pragma solidity ^0.8.30;

interface CopyEdgeVm {
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

contract CopyEdgeParityTest {
    CopyEdgeVm internal constant vm = CopyEdgeVm(address(uint160(uint256(keccak256("hevm cheat code")))));

    address internal constant TARGET = 0x1000000000000000000000000000000000000001;
    address internal constant WORKER = 0x2000000000000000000000000000000000000002;
    uint256 internal constant GAS_LIMIT = 1_000_000;

    function testReturndataCopyZeroLengthPastEndParity() public {
        bytes memory code = hex"5f60015f3e00";
        runCaseSkippingGas("returndatacopy-zero-length-past-end", code, hex"");
    }

    function testReturndataCopyZeroLengthMaxOffsetOutOfBoundsParity() public {
        bytes memory code = hex"5f7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff5f3e00";
        runCaseSkippingGas("returndatacopy-zero-length-max-offset-oob", code, hex"");
    }

    function testReturndataCopyExactEndZeroLengthNoExpansionParity() public {
        bytes memory code =
            hex"5f5f5f5f5f732000000000000000000000000000000000000002620f4240f1505f3d7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff3e595f5260205ff3";
        bytes memory accountCode = hex"602a5f5260205ff3";
        runCaseWithAccountCode("returndatacopy-exact-end-zero-length-no-expansion", code, hex"", WORKER, accountCode);
    }

    function testReturndataCopyMaxOffsetOutOfBoundsParity() public {
        bytes memory code = hex"60017fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff5f3e00";
        runCaseSkippingGas("returndatacopy-max-offset-oob", code, hex"");
    }

    function testReturndataCopyMemoryExpansionOogParity() public {
        bytes memory code = hex"5f5f5f5f5f732000000000000000000000000000000000000002620f4240f15060205f62ffffff3e";
        bytes memory accountCode = hex"602a5f5260205ff3";
        runCaseWithAccountCodeSkippingGas("returndatacopy-memory-expansion-oog", code, hex"", WORKER, accountCode);
    }

    function testCodeAndCalldataCopyPastEndZeroPaddingParity() public {
        bytes memory code =
            hex"7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff5f52600860025f37600860ff60203960405ff3";
        bytes memory data = hex"112233";
        runCase("code-calldata-copy-past-end-zero-padding", code, data);
    }

    function testCodeAndCalldataCopyZeroLengthMaxOffsetsNoExpansionParity() public {
        bytes memory code =
            hex"5f7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff395f7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff37595f5260205ff3";
        bytes memory data = hex"112233";
        runCase("code-calldata-copy-zero-length-max-offsets-no-expansion", code, data);
    }

    function testCalldataLoadMaxOffsetParity() public {
        bytes memory code = hex"7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff355f5260205ff3";
        bytes memory data = hex"112233";
        runCase("calldataload-max-offset-zero", code, data);
    }

    function testExtCodeCopyMissingAndPastEndZeroPaddingParity() public {
        bytes memory code =
            hex"7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff5f52600860025f7320000000000000000000000000000000000000023c60085f60207340000000000000000000000000000000000000043c60405ff3";
        bytes memory accountCode = hex"112233";
        runCaseWithAccountCode("extcodecopy-missing-past-end-zero-padding", code, hex"", WORKER, accountCode);
    }

    function testExtCodeCopyZeroLengthMaxOffsetsNoExpansionParity() public {
        bytes memory code =
            hex"5f7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7320000000000000000000000000000000000000023c595f5260205ff3";
        bytes memory accountCode = hex"112233";
        runCaseWithAccountCode("extcodecopy-zero-length-max-offsets-no-expansion", code, hex"", WORKER, accountCode);
    }

    function testMcopyZeroLengthHighOffsetsNoExpansionParity() public {
        bytes memory code =
            hex"5f7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff5e595f5260205ff3";
        runCase("mcopy-zero-length-high-offsets-no-expansion", code, hex"");
    }

    function testCallDataCopyMemoryExpansionOogParity() public {
        bytes memory code = hex"60205f62ffffff37";
        runCaseSkippingGas("calldatacopy-memory-expansion-oog", code, hex"112233");
    }

    function testCodeCopyMemoryExpansionOogParity() public {
        bytes memory code = hex"60205f62ffffff39";
        runCaseSkippingGas("codecopy-memory-expansion-oog", code, hex"");
    }

    function testMcopyMemoryExpansionOogParity() public {
        bytes memory code = hex"60205f62ffffff5e";
        runCaseSkippingGas("mcopy-memory-expansion-oog", code, hex"");
    }

    function testExtCodeCopyMemoryExpansionOogParity() public {
        bytes memory code = hex"60205f62ffffff7340000000000000000000000000000000000000043c";
        runCaseSkippingGas("extcodecopy-memory-expansion-oog", code, hex"");
    }

    function runCase(string memory name, bytes memory code, bytes memory data) internal {
        runCaseWithOptionalAccount(name, code, data, false, address(0), hex"");
    }

    function runCaseSkippingGas(string memory name, bytes memory code, bytes memory data) internal {
        runCaseWithOptionalAccount(name, code, data, true, address(0), hex"");
    }

    function runCaseWithAccountCode(
        string memory name,
        bytes memory code,
        bytes memory data,
        address account,
        bytes memory accountCode
    ) internal {
        runCaseWithOptionalAccount(name, code, data, false, account, accountCode);
    }

    function runCaseWithAccountCodeSkippingGas(
        string memory name,
        bytes memory code,
        bytes memory data,
        address account,
        bytes memory accountCode
    ) internal {
        runCaseWithOptionalAccount(name, code, data, true, account, accountCode);
    }

    function runCaseWithOptionalAccount(
        string memory name,
        bytes memory code,
        bytes memory data,
        bool skipGas,
        address account,
        bytes memory accountCode
    ) internal {
        bool hasAccountCode = account != address(0);
        if (hasAccountCode) {
            vm.etch(account, accountCode);
            require(account.code.length == accountCode.length, "account code not installed");
        }

        vm.etch(TARGET, code);
        require(TARGET.code.length == code.length, "runtime not installed");

        (bool success, bytes memory output) = TARGET.call{gas: GAS_LIMIT}(data);
        CopyEdgeVm.Gas memory gas = vm.lastCallGas();

        string[] memory command = new string[](43 + (skipGas ? 1 : 0) + (hasAccountCode ? 6 : 0));
        command[0] = "python3";
        command[1] = "../../bin/evm_parity.py";
        command[2] = "check";
        command[3] = "--case";
        command[4] = name;
        command[5] = "--code";
        command[6] = hexString(code);
        command[7] = "--calldata";
        command[8] = hexString(data);
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
        if (hasAccountCode) {
            command[cursor++] = "--account";
            command[cursor++] = string.concat(addressArg(account), "=", hexString(accountCode));
            command[cursor++] = "--warm-address";
            command[cursor++] = addressArg(account);
            command[cursor++] = "--expect-account-code";
            command[cursor++] = string.concat(addressArg(account), "=", hexString(accountCode));
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
