// SPDX-License-Identifier: MIT
pragma solidity ^0.8.30;

interface BitEdgeVm {
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

contract BitEdgeParityTest {
    BitEdgeVm internal constant vm = BitEdgeVm(address(uint160(uint256(keccak256("hevm cheat code")))));

    address internal constant TARGET = 0x1000000000000000000000000000000000000001;
    uint256 internal constant GAS_LIMIT = 1_000_000;

    function testByteAndSignextendHighIndexParity() public {
        bytes memory code = hex"608060200b5f5260805f0b60205261ffff60201a60405261ffff601f1a60605260805ff3";
        runCase("byte-signextend-high-index", code);
    }

    function testByteBoundaryIndicesParity() public {
        bytes32 word = hex"800102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1eff";
        bytes memory code = abi.encodePacked(
            hex"7f",
            word,
            hex"5f1a5f52",
            hex"7f",
            word,
            hex"601e1a602052",
            hex"7f",
            word,
            hex"601f1a604052",
            hex"7f",
            word,
            hex"60201a60605260805ff3"
        );
        runCase("byte-boundary-indices", code);
    }

    function testSignextendBoundaryBytesParity() public {
        bytes32 byte30SignBit = bytes32(uint256(1) << 247);
        bytes32 byte31SignBit = bytes32(uint256(1) << 255);
        bytes memory code = abi.encodePacked(
            hex"7f", byte30SignBit, hex"601e0b5f52", hex"7f", byte31SignBit, hex"601f0b60205260405ff3"
        );
        runCase("signextend-boundary-bytes", code);
    }

    function testShiftExact255BoundaryParity() public {
        bytes32 minInt = bytes32(uint256(1) << 255);
        bytes32 maxSigned = bytes32((uint256(1) << 255) - 1);
        bytes memory code = abi.encodePacked(
            hex"600160ff1b5f52",
            hex"7f",
            minInt,
            hex"60ff1c602052",
            hex"7f",
            minInt,
            hex"60ff1d604052",
            hex"7f",
            maxSigned,
            hex"60ff1d60605260805ff3"
        );
        runCase("shift-exact-255-boundary", code);
    }

    function testClzBoundaryWordsParity() public {
        bytes32 maxWord = bytes32(type(uint256).max);
        bytes32 secondTopBit = bytes32(uint256(1) << 254);
        bytes memory code = abi.encodePacked(
            hex"5f1e5f52",
            hex"7f",
            maxWord,
            hex"1e602052",
            hex"7f",
            secondTopBit,
            hex"1e604052",
            hex"60011e60605260805ff3"
        );
        runCase("clz-boundary-words", code);
    }

    function testUnsignedComparisonBoundaryParity() public {
        bytes32 maxWord = bytes32(type(uint256).max);
        bytes memory code = abi.encodePacked(
            hex"5f7f",
            maxWord,
            hex"105f52",
            hex"7f",
            maxWord,
            hex"5f10602052",
            hex"5f7f",
            maxWord,
            hex"11604052",
            hex"7f",
            maxWord,
            hex"5f11606052",
            hex"7f",
            maxWord,
            hex"7f",
            maxWord,
            hex"14608052",
            hex"7f",
            maxWord,
            hex"5f1460a052",
            hex"5f1560c052",
            hex"7f",
            maxWord,
            hex"1560e0526101005ff3"
        );
        runCase("unsigned-comparison-boundary", code);
    }

    function testSignedMinIntEdgesParity() public {
        bytes32 minInt = bytes32(uint256(1) << 255);
        bytes32 minusOne = bytes32(type(uint256).max);
        bytes memory code = abi.encodePacked(
            hex"7f",
            minusOne,
            hex"7f",
            minInt,
            hex"055f52",
            hex"7f",
            minusOne,
            hex"7f",
            minInt,
            hex"07602052",
            hex"5f7f",
            minInt,
            hex"12604052",
            hex"7f",
            minInt,
            hex"7f",
            minusOne,
            hex"13606052",
            hex"60805ff3"
        );
        runCase("signed-min-int-edges", code);
    }

    function testSignedComparisonBoundaryParity() public {
        bytes32 minInt = bytes32(uint256(1) << 255);
        bytes32 maxSigned = bytes32((uint256(1) << 255) - 1);
        bytes memory code = abi.encodePacked(
            hex"7f",
            maxSigned,
            hex"7f",
            minInt,
            hex"125f52",
            hex"7f",
            minInt,
            hex"7f",
            maxSigned,
            hex"13602052",
            hex"7f",
            minInt,
            hex"7f",
            maxSigned,
            hex"12604052",
            hex"7f",
            maxSigned,
            hex"7f",
            minInt,
            hex"1360605260805ff3"
        );
        runCase("signed-comparison-boundary", code);
    }

    function testSignedDivModSignCombinationsParity() public {
        bytes32 minusSeven = bytes32(type(uint256).max - 6);
        bytes32 minusThree = bytes32(type(uint256).max - 2);
        bytes memory code = abi.encodePacked(
            hex"6003",
            hex"7f",
            minusSeven,
            hex"055f52",
            hex"7f",
            minusThree,
            hex"600705602052",
            hex"7f",
            minusThree,
            hex"7f",
            minusSeven,
            hex"05604052",
            hex"6003",
            hex"7f",
            minusSeven,
            hex"07606052",
            hex"7f",
            minusThree,
            hex"600707608052",
            hex"7f",
            minusThree,
            hex"7f",
            minusSeven,
            hex"0760a05260c05ff3"
        );
        runCase("signed-divmod-sign-combinations", code);
    }

    function runCase(string memory name, bytes memory code) internal {
        vm.etch(TARGET, code);
        require(TARGET.code.length == code.length, "runtime not installed");

        (bool success, bytes memory output) = TARGET.call{gas: GAS_LIMIT}(hex"");
        BitEdgeVm.Gas memory gas = vm.lastCallGas();

        string[] memory command = new string[](43);
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
