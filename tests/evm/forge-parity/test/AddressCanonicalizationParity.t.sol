// SPDX-License-Identifier: MIT
pragma solidity ^0.8.30;

interface AddressCanonicalizationVm {
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
    function deal(address account, uint256 newBalance) external;
}

contract AddressCanonicalizationParityTest {
    AddressCanonicalizationVm internal constant vm =
        AddressCanonicalizationVm(address(uint160(uint256(keccak256("hevm cheat code")))));

    address internal constant TARGET = 0x1000000000000000000000000000000000000001;
    address internal constant WORKER = 0x2000000000000000000000000000000000000002;
    uint256 internal constant GAS_LIMIT = 1_000_000;

    function testHighBitsTruncatedForAccountReadParity() public {
        bytes memory workerCode = hex"602a5f5260205ff3";
        vm.deal(WORKER, 12345);
        bytes memory highWorker = highAddressWord(WORKER);
        bytes memory code = bytes.concat(hex"7f", highWorker, hex"315f527f", highWorker, hex"3b60205260405ff3");

        runCaseWithAccount("address-high-bits-account-read", code, workerCode, 12345);
    }

    function testHighBitsTruncatedForCallTargetParity() public {
        bytes memory workerCode = hex"602a5f5260205ff3";
        bytes memory code = bytes.concat(hex"60205f5f5f5f7f", highAddressWord(WORKER), hex"620f4240f160205260405ff3");

        runCaseWithAccount("address-high-bits-call-target", code, workerCode, 0);
    }

    function testHighBitsTruncatedForExtcodehashParity() public {
        bytes memory workerCode = hex"602a5f5260205ff3";
        bytes memory code = bytes.concat(hex"7f", highAddressWord(WORKER), hex"3f5f5260205ff3");
        string[] memory keccaks = new string[](1);
        keccaks[0] = keccakArg(workerCode, keccak256(workerCode));

        runCaseWithAccountAndKeccaks("address-high-bits-extcodehash", code, workerCode, 0, keccaks);
    }

    function testHighBitsTruncatedForPrecompileTargetParity() public {
        bytes memory code =
            bytes.concat(hex"602a5f526020602060205f5f7f", highAddressWord(address(0x04)), hex"620f4240f15f5260405ff3");

        runCase("address-high-bits-precompile-target", code, false, hex"", 0);
    }

    function testPrecompileAccountInspectionParity() public {
        bytes memory code = hex"6004315f5260043b60205260043f60405260605ff3";

        runCase("precompile-account-inspection", code, false, hex"", 0);
    }

    function testExtendedPrecompileAccountInspectionWarmParity() public {
        bytes memory code = hex"6011315f5260113b60205260113f604052610100316060526101003b6080526101003f60a05260c05ff3";

        runCase("extended-precompile-account-inspection-warm", code, false, hex"", 0);
    }

    function testHighBitsTruncatedForSelfdestructBeneficiaryParity() public {
        bytes memory code = bytes.concat(hex"7f", highAddressWord(WORKER), hex"ff");

        runCaseWithTargetBalance("address-high-bits-selfdestruct-beneficiary", code, true, hex"", 33, 777);
    }

    function runCaseWithAccount(string memory name, bytes memory code, bytes memory accountCode, uint256 accountBalance)
        internal
    {
        string[] memory emptyKeccaks = new string[](0);
        runCaseWithAccountAndKeccaks(name, code, accountCode, accountBalance, emptyKeccaks);
    }

    function runCaseWithAccountAndKeccaks(
        string memory name,
        bytes memory code,
        bytes memory accountCode,
        uint256 accountBalance,
        string[] memory keccakAssignments
    ) internal {
        if (accountBalance != 0) {
            vm.deal(WORKER, accountBalance);
        }
        vm.etch(WORKER, accountCode);
        require(WORKER.code.length == accountCode.length, "account code not installed");
        runCaseWithKeccaks(name, code, true, accountCode, accountBalance, keccakAssignments);
    }

    function runCase(
        string memory name,
        bytes memory code,
        bool hasAccount,
        bytes memory accountCode,
        uint256 accountBalance
    ) internal {
        string[] memory emptyKeccaks = new string[](0);
        runCaseWithKeccaks(name, code, hasAccount, accountCode, accountBalance, emptyKeccaks);
    }

    function runCaseWithKeccaks(
        string memory name,
        bytes memory code,
        bool hasAccount,
        bytes memory accountCode,
        uint256 accountBalance,
        string[] memory keccakAssignments
    ) internal {
        runCaseDetailed(name, code, hasAccount, accountCode, accountBalance, 0, keccakAssignments);
    }

    function runCaseWithTargetBalance(
        string memory name,
        bytes memory code,
        bool hasAccount,
        bytes memory accountCode,
        uint256 accountBalance,
        uint256 targetInitialBalance
    ) internal {
        string[] memory emptyKeccaks = new string[](0);
        if (accountBalance != 0) {
            vm.deal(WORKER, accountBalance);
        }
        vm.etch(WORKER, accountCode);
        require(WORKER.code.length == accountCode.length, "account code not installed");
        runCaseDetailed(name, code, hasAccount, accountCode, accountBalance, targetInitialBalance, emptyKeccaks);
    }

    function runCaseDetailed(
        string memory name,
        bytes memory code,
        bool hasAccount,
        bytes memory accountCode,
        uint256 accountBalance,
        uint256 targetInitialBalance,
        string[] memory keccakAssignments
    ) internal {
        vm.etch(TARGET, code);
        require(TARGET.code.length == code.length, "runtime not installed");
        if (targetInitialBalance != 0) {
            vm.deal(TARGET, targetInitialBalance);
        }

        (bool success, bytes memory output) = TARGET.call{gas: GAS_LIMIT}(hex"");
        AddressCanonicalizationVm.Gas memory gas = vm.lastCallGas();

        string[] memory command = new string[](43 + (hasAccount ? 10 : 0) + 2 * keccakAssignments.length);
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
        command[28] = uintToString(targetInitialBalance);
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
        if (hasAccount) {
            command[cursor++] = "--account";
            command[cursor++] = string.concat(addressArg(WORKER), "=", hexString(accountCode));
            command[cursor++] = "--account-balance";
            command[cursor++] = string.concat(addressArg(WORKER), "=", uintToString(accountBalance));
            command[cursor++] = "--warm-address";
            command[cursor++] = addressArg(WORKER);
            command[cursor++] = "--expect-account-code";
            command[cursor++] = string.concat(addressArg(WORKER), "=", hexString(accountCode));
            command[cursor++] = "--expect-account-balance";
            command[cursor++] = string.concat(addressArg(WORKER), "=", uintToString(WORKER.balance));
        }
        for (uint256 i = 0; i < keccakAssignments.length; i++) {
            command[cursor++] = "--keccak";
            command[cursor++] = keccakAssignments[i];
        }

        vm.ffi(command);
    }

    function highAddressWord(address value) internal pure returns (bytes memory) {
        return abi.encodePacked(hex"ffffffffffffffffffffffff", value);
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

    function keccakArg(bytes memory data, bytes32 hash) internal pure returns (string memory) {
        return string.concat(hexString(data), "=", wordHex(hash));
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
