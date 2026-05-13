// SPDX-License-Identifier: MIT
pragma solidity ^0.8.30;

interface TransientStorageVm {
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

contract TransientStorageParityTest {
    TransientStorageVm internal constant vm =
        TransientStorageVm(address(uint160(uint256(keccak256("hevm cheat code")))));

    address internal constant TARGET = 0x1000000000000000000000000000000000000001;
    address internal constant WORKER = 0x2000000000000000000000000000000000000002;
    uint256 internal constant GAS_LIMIT = 1_000_000;

    function testRootTransientStorageClearsAfterSuccessParity() public {
        bytes memory code = hex"60ab5f5d00";
        runRootTransientCase("root-transient-success-clears", code, bytes32(0));
    }

    function testRootRevertRollsBackTransientStorageParity() public {
        bytes memory code = hex"60ab5f5d5f5ffd";
        runRootTransientCase("root-revert-rolls-back-transient-storage", code, bytes32(0));
    }

    function testRootInvalidRollsBackTransientStorageParity() public {
        bytes memory code = hex"60ab5f5dfe";
        runRootTransientCaseSkippingGas("root-invalid-rolls-back-transient-storage", code, bytes32(0));
    }

    function testRootMemoryOogRollsBackTransientStorageParity() public {
        bytes memory code = hex"60ab5f5d600162ffffff52";
        runRootTransientCaseSkippingGas("root-memory-oog-rolls-back-transient-storage", code, bytes32(0));
    }

    function testTransientStoragePersistsAcrossSuccessfulCallFramesParity() public {
        bytes memory code =
            hex"5f5f5f5f5f732000000000000000000000000000000000000002620f4240f15060205f60015f5f732000000000000000000000000000000000000002620f4240f15060205ff3";
        bytes memory accountCode = hex"3615600d575f5c5f5260205ff35b60ab5f5d00";
        runCaseWithAccountCode("transient-call-commit", code, WORKER, accountCode);
    }

    function testTransientStorageRollsBackAfterRevertedCallFrameParity() public {
        bytes memory code =
            hex"5f5f5f5f5f732000000000000000000000000000000000000002620f4240f15060205f60015f5f732000000000000000000000000000000000000002620f4240f15060205ff3";
        bytes memory accountCode = hex"3615600d575f5c5f5260205ff35b60ab5f5d5f5ffd";
        runCaseWithAccountCode("transient-call-revert-rollback", code, WORKER, accountCode);
    }

    function testTransientStorageDelegatecallUsesCallerContextParity() public {
        bytes memory code = hex"5f5f5f5f732000000000000000000000000000000000000002620f4240f4505f5c5f5260205ff3";
        bytes memory accountCode = hex"60cd5f5d00";
        runCaseWithAccountCode("transient-delegatecall-caller-context", code, WORKER, accountCode);
    }

    function testTransientStorageCallcodeUsesCallerContextParity() public {
        bytes memory code = hex"5f5f5f5f5f732000000000000000000000000000000000000002620f4240f2505f5c5f5260205ff3";
        bytes memory accountCode = hex"60ef5f5d00";
        runCaseWithAccountCode("transient-callcode-caller-context", code, WORKER, accountCode);
    }

    function testTransientStorageCallcodeRevertRollsBackCallerContextParity() public {
        bytes memory code = hex"5f5f5f5f5f732000000000000000000000000000000000000002620f4240f25f525f5c60205260405ff3";
        bytes memory accountCode = hex"60015f5d5f5ffd";
        runCaseWithAccountCode("transient-callcode-revert-rolls-back-caller-context", code, WORKER, accountCode);
    }

    function testTransientStorageCallcodeInvalidRollsBackCallerContextParity() public {
        bytes memory code = hex"5f5f5f5f5f732000000000000000000000000000000000000002620f4240f25f525f5c60205260405ff3";
        bytes memory accountCode = hex"60015f5dfe";
        runCaseWithAccountCode("transient-callcode-invalid-rolls-back-caller-context", code, WORKER, accountCode);
    }

    function testTransientStorageCallcodeMemoryOogRollsBackCallerContextParity() public {
        bytes memory code = hex"5f5f5f5f5f732000000000000000000000000000000000000002620f4240f25f525f5c60205260405ff3";
        bytes memory accountCode = hex"60015f5d600162ffffff52";
        runCaseWithAccountCode("transient-callcode-memory-oog-rolls-back-caller-context", code, WORKER, accountCode);
    }

    function testTransientStorageDelegatecallRevertRollsBackCallerContextParity() public {
        bytes memory code = hex"5f5f5f5f732000000000000000000000000000000000000002620f4240f45f525f5c60205260405ff3";
        bytes memory accountCode = hex"60015f5d5f5ffd";
        runCaseWithAccountCode("transient-delegatecall-revert-rolls-back-caller-context", code, WORKER, accountCode);
    }

    function testTransientStorageDelegatecallInvalidRollsBackCallerContextParity() public {
        bytes memory code = hex"5f5f5f5f732000000000000000000000000000000000000002620f4240f45f525f5c60205260405ff3";
        bytes memory accountCode = hex"60015f5dfe";
        runCaseWithAccountCode("transient-delegatecall-invalid-rolls-back-caller-context", code, WORKER, accountCode);
    }

    function testTransientStorageDelegatecallMemoryOogRollsBackCallerContextParity() public {
        bytes memory code = hex"5f5f5f5f732000000000000000000000000000000000000002620f4240f45f525f5c60205260405ff3";
        bytes memory accountCode = hex"60015f5d600162ffffff52";
        runCaseWithAccountCode("transient-delegatecall-memory-oog-rolls-back-caller-context", code, WORKER, accountCode);
    }

    function testStaticcallRejectsTransientStoreParity() public {
        bytes memory code = hex"5f5f5f5f732000000000000000000000000000000000000002620f4240fa5f5260205ff3";
        bytes memory accountCode = hex"60ab5f5d00";
        runCaseWithAccountCode("staticcall-rejects-transient-store", code, WORKER, accountCode);
    }

    function runCaseWithAccountCode(string memory name, bytes memory code, address account, bytes memory accountCode)
        internal
    {
        vm.etch(account, accountCode);
        vm.etch(TARGET, code);
        require(account.code.length == accountCode.length, "account code not installed");
        require(TARGET.code.length == code.length, "runtime not installed");

        (bool success, bytes memory output) = TARGET.call{gas: GAS_LIMIT}(hex"");
        TransientStorageVm.Gas memory gas = vm.lastCallGas();

        string[] memory command = new string[](49);
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
        command[43] = "--account";
        command[44] = string.concat(addressArg(account), "=", hexString(accountCode));
        command[45] = "--warm-address";
        command[46] = addressArg(account);
        command[47] = "--expect-account-code";
        command[48] = string.concat(addressArg(account), "=", hexString(accountCode));

        vm.ffi(command);
    }

    function runRootTransientCase(string memory name, bytes memory code, bytes32 expectedSlot) internal {
        runRootTransientCaseWithGasMode(name, code, expectedSlot, false);
    }

    function runRootTransientCaseSkippingGas(string memory name, bytes memory code, bytes32 expectedSlot) internal {
        runRootTransientCaseWithGasMode(name, code, expectedSlot, true);
    }

    function runRootTransientCaseWithGasMode(string memory name, bytes memory code, bytes32 expectedSlot, bool skipGas)
        internal
    {
        vm.etch(TARGET, code);
        require(TARGET.code.length == code.length, "runtime not installed");

        (bool success, bytes memory output) = TARGET.call{gas: GAS_LIMIT}(hex"");
        TransientStorageVm.Gas memory gas = vm.lastCallGas();

        string[] memory command = new string[](45 + (skipGas ? 1 : 0));
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
        command[43] = "--expect-transient-storage";
        command[44] = string.concat(wordHex(bytes32(0)), "=", wordHex(expectedSlot));
        if (skipGas) {
            command[45] = "--skip-gas";
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
