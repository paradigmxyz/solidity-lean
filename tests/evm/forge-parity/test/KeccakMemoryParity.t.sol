// SPDX-License-Identifier: MIT
pragma solidity ^0.8.30;

interface KeccakMemoryVm {
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

contract KeccakMemoryParityTest {
    KeccakMemoryVm internal constant vm = KeccakMemoryVm(address(uint160(uint256(keccak256("hevm cheat code")))));

    address internal constant TARGET = 0x1000000000000000000000000000000000000001;
    uint256 internal constant GAS_LIMIT = 1_000_000;

    function testKeccakZeroLengthHighOffsetNoExpansionParity() public {
        bytes memory code = hex"5f62ffffff205f5260205ff3";
        bytes memory empty = hex"";
        string[] memory keccaks = new string[](1);
        keccaks[0] = keccakArg(empty, keccak256(empty));
        runCaseWithKeccaks("keccak-zero-length-high-offset-no-expansion", code, keccaks);
    }

    function testKeccakZeroLengthMaxOffsetNoExpansionParity() public {
        bytes memory code = abi.encodePacked(hex"5f7f", bytes32(type(uint256).max), hex"205f5260205ff3");
        bytes memory empty = hex"";
        string[] memory keccaks = new string[](1);
        keccaks[0] = keccakArg(empty, keccak256(empty));
        runCaseWithKeccaks("keccak-zero-length-max-offset-no-expansion", code, keccaks);
    }

    function testKeccakMemoryExpansionZeroPaddingParity() public {
        bytes memory code = hex"60ab5f536101205f205f5260205ff3";
        bytes memory preimage = new bytes(0x120);
        preimage[0] = bytes1(0xab);
        string[] memory keccaks = new string[](1);
        keccaks[0] = keccakArg(preimage, keccak256(preimage));
        runCaseWithKeccaks("keccak-memory-expansion-zero-padding", code, keccaks);
    }

    function testKeccakMemoryExpansionOogDoesNotNeedOracleParity() public {
        bytes memory code = hex"602062ffffff20";
        string[] memory keccaks = new string[](0);
        runCaseWithGasPolicy("keccak-memory-expansion-oog-no-oracle", code, keccaks, true);
    }

    function runCaseWithKeccaks(string memory name, bytes memory code, string[] memory keccakAssignments) internal {
        runCaseWithGasPolicy(name, code, keccakAssignments, false);
    }

    function runCaseWithGasPolicy(
        string memory name,
        bytes memory code,
        string[] memory keccakAssignments,
        bool skipGas
    ) internal {
        vm.etch(TARGET, code);
        require(TARGET.code.length == code.length, "runtime not installed");

        (bool success, bytes memory output) = TARGET.call{gas: GAS_LIMIT}(hex"");
        KeccakMemoryVm.Gas memory gas = vm.lastCallGas();

        string[] memory command = new string[](43 + (skipGas ? 1 : 0) + 2 * keccakAssignments.length);
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
        for (uint256 i = 0; i < keccakAssignments.length; i++) {
            command[cursor++] = "--keccak";
            command[cursor++] = keccakAssignments[i];
        }

        vm.ffi(command);
    }

    function keccakArg(bytes memory input, bytes32 output) internal pure returns (string memory) {
        return string.concat(hexString(input), "=", wordHex(output));
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
