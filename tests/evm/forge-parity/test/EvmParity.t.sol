// SPDX-License-Identifier: MIT
pragma solidity ^0.8.30;

interface Vm {
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
    function store(address target, bytes32 slot, bytes32 value) external;
    function load(address target, bytes32 slot) external view returns (bytes32 value);
    function etch(address target, bytes calldata newRuntimeBytecode) external;
    function coolSlot(address target, bytes32 slot) external;
    function deal(address target, uint256 newBalance) external;
    function getNonce(address target) external view returns (uint64 nonce);
    function recordLogs() external;
    function getRecordedLogs() external view returns (Log[] memory logs);
}

contract ComplexParitySubject {
    uint256 public total;
    uint256 public seed;
    uint256 public flag;

    event Mixed(uint256 indexed rounds, uint256 indexed mode, uint256 value, uint256 seed);

    error TooSmall(uint256 got, uint256 need);

    function pureLoop(uint256 rounds, uint256 x) external pure returns (uint256) {
        uint256 acc = x + 3;
        for (uint256 i = 0; i < rounds; i++) {
            if (i & 1 == 0) {
                acc = (acc * 3 + i) ^ (acc >> 1);
            } else {
                acc = (acc + i * 7) ^ (acc << 2);
            }

            if (acc & 0xff == 0x42) {
                acc += 0x99;
            } else if (acc & 0x0f == 0x0a) {
                acc ^= 0x1234;
            } else {
                acc += rounds - i;
            }
        }

        uint256 j = rounds;
        while (j > 0) {
            acc = (acc ^ j) + (j << 3);
            unchecked {
                j--;
            }
        }
        return acc;
    }

    function memoryCrunch(uint256 a, uint256 b, uint256 rounds)
        external
        pure
        returns (uint256 sum, uint256 folded, uint256 last)
    {
        uint256[8] memory ring;
        ring[0] = a;
        ring[1] = b;
        sum = a + b;

        for (uint256 i = 2; i < rounds + 2; i++) {
            uint256 left = ring[(i - 1) & 7];
            uint256 right = ring[(i - 2) & 7];
            uint256 next = left + right + i * 11;
            ring[i & 7] = next;
            sum += next;
            folded ^= (next << (i & 7)) | (next >> ((i + 1) & 7));
        }

        last = ring[(rounds + 1) & 7];
    }

    function bytesLoop(bytes calldata data, uint256 salt) external pure returns (uint256 acc) {
        acc = salt ^ data.length;
        for (uint256 i = 0; i < data.length; i++) {
            uint256 value = uint8(data[i]);
            if (value & 1 == 0) {
                acc += value * (i + 1);
            } else {
                acc ^= value << (i & 15);
            }
            acc = (acc << 1) ^ (acc >> 3) ^ 0x55;
        }
    }

    function storageMix(uint256 rounds, uint256 inc) external returns (uint256 out) {
        uint256 local = total;
        uint256 localSeed = seed;

        for (uint256 i = 0; i < rounds; i++) {
            local += inc + i;
            if (local & 1 == 0) {
                localSeed ^= local + (i << 4);
            } else {
                localSeed += (local ^ i) & 0xffff;
            }
        }

        flag = (localSeed & 1) + rounds;
        total = local;
        seed = localSeed;
        emit Mixed(rounds, flag, local, localSeed);
        return local ^ localSeed ^ flag;
    }

    function guarded(uint256 value, uint256 minimum) external pure returns (uint256) {
        if (value < minimum) {
            revert TooSmall(value, minimum);
        }
        return (value - minimum) * 17 + 1;
    }
}

interface IWorkerParitySubject {
    function bump(uint256 rounds, uint256 inc) external returns (uint256);
    function takeValue(uint256 rounds) external payable returns (uint256);
    function readSum(uint256 rounds) external view returns (uint256);
    function failWith(uint256 value) external pure;
}

contract WorkerParitySubject {
    uint256 public total;
    uint256 public seed;

    event WorkerTouched(address indexed caller, uint256 indexed rounds, uint256 total, uint256 seed);

    error WorkerError(uint256 value);

    function bump(uint256 rounds, uint256 inc) external returns (uint256 out) {
        uint256 local = total;
        uint256 localSeed = seed;
        for (uint256 i = 0; i < rounds; i++) {
            local += inc + i;
            if (local & 1 == 0) {
                localSeed ^= local + (i << 5);
            } else {
                localSeed += (local ^ i) & 0xffff;
            }
        }
        total = local;
        seed = localSeed;
        emit WorkerTouched(msg.sender, rounds, local, localSeed);
        return local ^ localSeed;
    }

    function takeValue(uint256 rounds) external payable returns (uint256 out) {
        uint256 local = total + msg.value;
        uint256 localSeed = seed ^ address(this).balance;
        for (uint256 i = 0; i < rounds; i++) {
            local += i + 1;
            localSeed = (localSeed + local) ^ (i << 6);
        }
        total = local;
        seed = localSeed;
        emit WorkerTouched(msg.sender, rounds, local, localSeed);
        return local ^ localSeed ^ address(this).balance;
    }

    function readSum(uint256 rounds) external view returns (uint256 out) {
        out = total + seed + rounds;
        for (uint256 i = 0; i < rounds; i++) {
            out = (out + i * 13) ^ (out >> 2);
        }
    }

    function failWith(uint256 value) external pure {
        revert WorkerError(value);
    }
}

contract DelegateParityLib {
    event DelegateTouched(address indexed caller, uint256 value, uint256 result);

    function writeViaDelegate(uint256 value) external returns (uint256) {
        uint256 next = value * 3 + 11;
        assembly {
            sstore(0, next)
        }
        emit DelegateTouched(msg.sender, value, next);
        return next;
    }
}

contract MultiCallerParitySubject {
    address internal constant WORKER = 0x2000000000000000000000000000000000000002;
    address internal constant DELEGATE_LIB = 0x3000000000000000000000000000000000000003;

    uint256 public localTotal;
    uint256 public last;

    event CallerTouched(uint256 indexed mode, uint256 value);

    function callWorker(uint256 rounds, uint256 inc) external returns (uint256) {
        uint256 beforeValue = IWorkerParitySubject(WORKER).readSum(3);
        uint256 workerValue = IWorkerParitySubject(WORKER).bump(rounds, inc);
        last = beforeValue + workerValue + localTotal;
        emit CallerTouched(1, last);
        return last;
    }

    function sendValueToWorker(uint256 amount, uint256 rounds) external returns (uint256) {
        uint256 workerValue = IWorkerParitySubject(WORKER).takeValue{value: amount}(rounds);
        last = workerValue + address(this).balance;
        emit CallerTouched(4, last);
        return last;
    }

    function staticWorker(uint256 rounds) external view returns (uint256) {
        return IWorkerParitySubject(WORKER).readSum(rounds) + localTotal;
    }

    function catchWorkerRevert(uint256 value) external returns (uint256 length, bytes4 selector) {
        (bool ok, bytes memory data) = WORKER.call(abi.encodeCall(IWorkerParitySubject.failWith, (value)));
        if (ok) {
            last = 0;
            return (0, bytes4(0));
        }
        bytes4 sel;
        assembly {
            sel := mload(add(data, 32))
        }
        last = data.length;
        emit CallerTouched(2, data.length);
        return (data.length, sel);
    }

    function delegateWrite(uint256 value) external returns (uint256) {
        (bool ok, bytes memory data) =
            DELEGATE_LIB.delegatecall(abi.encodeWithSignature("writeViaDelegate(uint256)", value));
        require(ok, "delegate failed");
        uint256 written = abi.decode(data, (uint256));
        last = written + localTotal;
        emit CallerTouched(3, last);
        return last;
    }
}

contract CreatedParitySubject {
    uint256 public value;

    event ConstructorTouched(address indexed caller, uint256 value);
    event RuntimeTouched(address indexed caller, uint256 rounds, uint256 value);

    constructor(uint256 seed) payable {
        value = seed + msg.value;
        emit ConstructorTouched(msg.sender, value);
    }

    function touch(uint256 rounds, uint256 inc) external returns (uint256 out) {
        uint256 local = value;
        for (uint256 i = 0; i < rounds; i++) {
            local += inc + i;
            local = (local ^ (i << 7)) + address(this).balance;
        }
        value = local;
        emit RuntimeTouched(msg.sender, rounds, local);
        return local ^ address(this).balance;
    }
}

contract CreateParityFactory {
    address public lastCreated;
    uint256 public lastValue;

    event FactoryDeployed(address indexed created, uint256 value);

    function deployCreate(uint256 amount, uint256 seed, uint256 rounds, uint256 inc)
        external
        returns (address created, uint256 out)
    {
        CreatedParitySubject child = new CreatedParitySubject{value: amount}(seed);
        created = address(child);
        out = child.touch(rounds, inc);
        lastCreated = created;
        lastValue = out;
        emit FactoryDeployed(created, out);
    }

    function deployCreate2(bytes32 salt, uint256 amount, uint256 seed, uint256 rounds, uint256 inc)
        external
        returns (address created, uint256 out)
    {
        CreatedParitySubject child = new CreatedParitySubject{salt: salt, value: amount}(seed);
        created = address(child);
        out = child.touch(rounds, inc);
        lastCreated = created;
        lastValue = out;
        emit FactoryDeployed(created, out);
    }
}

contract PrecompileParitySubject {
    function identity(bytes calldata input) external view returns (bool ok, bytes memory output) {
        return address(4).staticcall(input);
    }
}

contract EvmParityTest {
    Vm internal constant vm = Vm(address(uint160(uint256(keccak256("hevm cheat code")))));

    address internal constant TARGET = 0x1000000000000000000000000000000000000001;
    address internal constant WORKER = 0x2000000000000000000000000000000000000002;
    address internal constant DELEGATE_LIB = 0x3000000000000000000000000000000000000003;
    uint256 internal constant GAS_LIMIT = 1_000_000;

    struct DynamicCreateCase {
        string name;
        bytes data;
        uint256 rootInitialBalance;
        uint64 rootNonce;
        address expectedCreated;
        string[] keccakAssignments;
    }

    struct BaseCommandCase {
        string name;
        bytes code;
        bytes data;
        bool success;
        bytes output;
        Vm.Gas gas;
        uint256 callValue;
        uint256 initialBalance;
        uint256 expectedBalance;
    }

    function testReturnWordParity() public {
        bytes memory code = hex"602a5f5260205ff3";
        runCase("return-word", code, hex"", new bytes32[](0), new bytes32[](0));
    }

    function testGasOpcodeParity() public {
        bytes memory code = hex"5a5f5260205ff3";
        runCase("gas-opcode", code, hex"", new bytes32[](0), new bytes32[](0));
    }

    function testColdSstoreParity() public {
        bytes memory code = hex"602a5f5500";
        bytes32[] memory initialSlots = new bytes32[](0);
        bytes32[] memory checkedSlots = new bytes32[](1);
        checkedSlots[0] = bytes32(uint256(0));
        runCase("cold-sstore", code, hex"", initialSlots, checkedSlots);
    }

    function testColdSloadParity() public {
        bytes memory code = hex"5f545f5260205ff3";
        bytes32[] memory initialSlots = new bytes32[](1);
        initialSlots[0] = bytes32(uint256(7));
        bytes32[] memory checkedSlots = new bytes32[](1);
        checkedSlots[0] = bytes32(uint256(0));
        runCase("cold-sload", code, hex"", initialSlots, checkedSlots);
    }

    function testLogParity() public {
        bytes memory code = hex"602a5f52600760205fa100";
        runCase("log1", code, hex"", new bytes32[](0), new bytes32[](0));
    }

    function testSelfbalanceParity() public {
        bytes memory code = hex"475f5260205ff3";
        runCaseWithState("selfbalance", code, hex"", 123, 0, new bytes32[](0), new bytes32[](0));
    }

    function testRevertParity() public {
        bytes memory code = hex"602a5f5260205ffd";
        runCase("revert-word", code, hex"", new bytes32[](0), new bytes32[](0));
    }

    function testComplexPureLoopContractParity() public {
        runCase(
            "complex-pure-loop",
            type(ComplexParitySubject).runtimeCode,
            abi.encodeCall(ComplexParitySubject.pureLoop, (19, 7)),
            new bytes32[](0),
            new bytes32[](0)
        );
    }

    function testComplexMemoryCrunchContractParity() public {
        runCase(
            "complex-memory-crunch",
            type(ComplexParitySubject).runtimeCode,
            abi.encodeCall(ComplexParitySubject.memoryCrunch, (9, 13, 12)),
            new bytes32[](0),
            new bytes32[](0)
        );
    }

    function testComplexBytesLoopContractParity() public {
        runCase(
            "complex-bytes-loop",
            type(ComplexParitySubject).runtimeCode,
            abi.encodeCall(ComplexParitySubject.bytesLoop, (hex"00112233445566778899aabbccddeeff", 0x1234)),
            new bytes32[](0),
            new bytes32[](0)
        );
    }

    function testComplexStorageAndLogContractParity() public {
        bytes32[] memory initialSlots = new bytes32[](3);
        initialSlots[0] = bytes32(uint256(3));
        initialSlots[1] = bytes32(uint256(11));
        initialSlots[2] = bytes32(uint256(0));

        bytes32[] memory checkedSlots = new bytes32[](3);
        checkedSlots[0] = bytes32(uint256(0));
        checkedSlots[1] = bytes32(uint256(1));
        checkedSlots[2] = bytes32(uint256(2));

        runCase(
            "complex-storage-log",
            type(ComplexParitySubject).runtimeCode,
            abi.encodeCall(ComplexParitySubject.storageMix, (8, 5)),
            initialSlots,
            checkedSlots
        );
    }

    function testComplexCustomErrorRevertContractParity() public {
        runCase(
            "complex-custom-error",
            type(ComplexParitySubject).runtimeCode,
            abi.encodeCall(ComplexParitySubject.guarded, (5, 9)),
            new bytes32[](0),
            new bytes32[](0)
        );
    }

    function testMultiContractCallAndStaticCallParity() public {
        bytes32[] memory rootInitialSlots = new bytes32[](2);
        rootInitialSlots[0] = bytes32(uint256(17));
        rootInitialSlots[1] = bytes32(uint256(0));

        bytes32[] memory rootCheckedSlots = new bytes32[](2);
        rootCheckedSlots[0] = bytes32(uint256(0));
        rootCheckedSlots[1] = bytes32(uint256(1));

        bytes32[] memory workerInitialSlots = new bytes32[](2);
        workerInitialSlots[0] = bytes32(uint256(5));
        workerInitialSlots[1] = bytes32(uint256(9));

        bytes32[] memory workerCheckedSlots = new bytes32[](2);
        workerCheckedSlots[0] = bytes32(uint256(0));
        workerCheckedSlots[1] = bytes32(uint256(1));

        runMultiCase(
            "multi-call-static",
            abi.encodeCall(MultiCallerParitySubject.callWorker, (6, 4)),
            rootInitialSlots,
            rootCheckedSlots,
            workerInitialSlots,
            workerCheckedSlots
        );
    }

    function testMultiContractStaticOnlyParity() public {
        bytes32[] memory workerInitialSlots = new bytes32[](2);
        workerInitialSlots[0] = bytes32(uint256(21));
        workerInitialSlots[1] = bytes32(uint256(34));

        runMultiCase(
            "multi-static-only",
            abi.encodeCall(MultiCallerParitySubject.staticWorker, (9)),
            new bytes32[](0),
            new bytes32[](0),
            workerInitialSlots,
            new bytes32[](0)
        );
    }

    function testMultiContractValueTransferParity() public {
        bytes32[] memory rootCheckedSlots = new bytes32[](1);
        rootCheckedSlots[0] = bytes32(uint256(1));

        bytes32[] memory workerInitialSlots = new bytes32[](2);
        workerInitialSlots[0] = bytes32(uint256(2));
        workerInitialSlots[1] = bytes32(uint256(6));

        bytes32[] memory workerCheckedSlots = new bytes32[](2);
        workerCheckedSlots[0] = bytes32(uint256(0));
        workerCheckedSlots[1] = bytes32(uint256(1));

        vm.deal(TARGET, 5000);
        runMultiCase(
            "multi-value-transfer",
            abi.encodeCall(MultiCallerParitySubject.sendValueToWorker, (1234, 5)),
            new bytes32[](0),
            rootCheckedSlots,
            workerInitialSlots,
            workerCheckedSlots
        );
    }

    function testMultiContractCaughtRevertParity() public {
        bytes32[] memory rootCheckedSlots = new bytes32[](1);
        rootCheckedSlots[0] = bytes32(uint256(1));

        runMultiCase(
            "multi-caught-revert",
            abi.encodeCall(MultiCallerParitySubject.catchWorkerRevert, (77)),
            new bytes32[](0),
            rootCheckedSlots,
            new bytes32[](0),
            new bytes32[](0)
        );
    }

    function testMultiContractDelegateCallParity() public {
        bytes32[] memory rootInitialSlots = new bytes32[](2);
        rootInitialSlots[0] = bytes32(uint256(4));
        rootInitialSlots[1] = bytes32(uint256(1));

        bytes32[] memory rootCheckedSlots = new bytes32[](2);
        rootCheckedSlots[0] = bytes32(uint256(0));
        rootCheckedSlots[1] = bytes32(uint256(1));

        runMultiCase(
            "multi-delegatecall",
            abi.encodeCall(MultiCallerParitySubject.delegateWrite, (19)),
            rootInitialSlots,
            rootCheckedSlots,
            new bytes32[](0),
            new bytes32[](0)
        );
    }

    function testIdentityPrecompileParity() public {
        runCase(
            "identity-precompile",
            type(PrecompileParitySubject).runtimeCode,
            abi.encodeCall(PrecompileParitySubject.identity, (hex"00112233445566778899aabbccddeeff")),
            new bytes32[](0),
            new bytes32[](0)
        );
    }

    function testDynamicCreateParity() public {
        bytes memory data = abi.encodeCall(CreateParityFactory.deployCreate, (777, 11, 4, 3));
        installRuntime(type(CreateParityFactory).runtimeCode);
        vm.deal(TARGET, 5000);

        uint64 nonce = vm.getNonce(TARGET);
        bytes memory preimage = createAddressPreimage(TARGET, nonce);
        address expectedCreated = address(uint160(uint256(keccak256(preimage))));

        string[] memory keccaks = new string[](1);
        keccaks[0] = keccakArg(preimage, keccak256(preimage));
        runDynamicCreateCase(
            DynamicCreateCase({
                name: "dynamic-create",
                data: data,
                rootInitialBalance: 5000,
                rootNonce: nonce,
                expectedCreated: expectedCreated,
                keccakAssignments: keccaks
            })
        );
    }

    function testDynamicCreate2Parity() public {
        bytes32 salt = bytes32(uint256(0xabc123));
        uint256 seed = 17;
        bytes memory data = abi.encodeCall(CreateParityFactory.deployCreate2, (salt, 999, seed, 5, 4));
        bytes memory initCode = abi.encodePacked(type(CreatedParitySubject).creationCode, abi.encode(seed));
        bytes32 initHash = keccak256(initCode);

        installRuntime(type(CreateParityFactory).runtimeCode);
        vm.deal(TARGET, 7000);

        uint64 nonce = vm.getNonce(TARGET);
        bytes memory preimage = create2AddressPreimage(TARGET, salt, initHash);
        address expectedCreated = address(uint160(uint256(keccak256(preimage))));

        string[] memory keccaks = new string[](2);
        keccaks[0] = keccakArg(initCode, initHash);
        keccaks[1] = keccakArg(preimage, keccak256(preimage));
        runDynamicCreateCase(
            DynamicCreateCase({
                name: "dynamic-create2",
                data: data,
                rootInitialBalance: 7000,
                rootNonce: nonce,
                expectedCreated: expectedCreated,
                keccakAssignments: keccaks
            })
        );
    }

    function runCase(
        string memory name,
        bytes memory code,
        bytes memory data,
        bytes32[] memory initialSlotValues,
        bytes32[] memory checkedSlots
    ) internal {
        runCaseWithState(name, code, data, 0, 0, initialSlotValues, checkedSlots);
    }

    function runCaseWithState(
        string memory name,
        bytes memory code,
        bytes memory data,
        uint256 initialBalance,
        uint256 callValue,
        bytes32[] memory initialSlotValues,
        bytes32[] memory checkedSlots
    ) internal {
        address target = installRuntime(code);
        vm.deal(target, initialBalance);
        for (uint256 i = 0; i < initialSlotValues.length; i++) {
            vm.store(target, bytes32(i), initialSlotValues[i]);
            vm.coolSlot(target, bytes32(i));
        }

        vm.recordLogs();
        (bool success, bytes memory output) = target.call{gas: GAS_LIMIT, value: callValue}(data);
        Vm.Gas memory gas = vm.lastCallGas();
        Vm.Log[] memory logs = vm.getRecordedLogs();

        string[] memory command =
            new string[](31 + 4 * initialSlotValues.length + 2 * checkedSlots.length + 2 * logs.length);
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
        command[10] = uintToString(GAS_LIMIT);
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
        command[22] = hexString(abi.encodePacked(address(this)));
        command[23] = "--origin";
        command[24] = hexString(abi.encodePacked(tx.origin));
        command[25] = "--callvalue";
        command[26] = uintToString(callValue);
        command[27] = "--balance";
        command[28] = uintToString(initialBalance + callValue);
        command[29] = "--expect-balance";
        command[30] = uintToString(target.balance);

        uint256 cursor = 31;
        for (uint256 i = 0; i < initialSlotValues.length; i++) {
            command[cursor++] = "--storage";
            command[cursor++] = string.concat(wordHex(bytes32(i)), "=", wordHex(initialSlotValues[i]));
            command[cursor++] = "--original-storage";
            command[cursor++] = string.concat(wordHex(bytes32(i)), "=", wordHex(bytes32(0)));
        }
        for (uint256 i = 0; i < checkedSlots.length; i++) {
            bytes32 slot = checkedSlots[i];
            command[cursor++] = "--expect-storage";
            command[cursor++] = string.concat(wordHex(slot), "=", wordHex(vm.load(target, slot)));
        }
        for (uint256 i = 0; i < logs.length; i++) {
            command[cursor++] = "--expect-log";
            command[cursor++] = logSpec(logs[i]);
        }

        vm.ffi(command);
    }

    function runMultiCase(
        string memory name,
        bytes memory data,
        bytes32[] memory rootInitialSlotValues,
        bytes32[] memory rootCheckedSlots,
        bytes32[] memory workerInitialSlotValues,
        bytes32[] memory workerCheckedSlots
    ) internal {
        installRuntime(type(MultiCallerParitySubject).runtimeCode);
        vm.etch(WORKER, type(WorkerParitySubject).runtimeCode);
        vm.etch(DELEGATE_LIB, type(DelegateParityLib).runtimeCode);

        for (uint256 i = 0; i < rootInitialSlotValues.length; i++) {
            vm.store(TARGET, bytes32(i), rootInitialSlotValues[i]);
            vm.coolSlot(TARGET, bytes32(i));
        }
        for (uint256 i = 0; i < workerInitialSlotValues.length; i++) {
            vm.store(WORKER, bytes32(i), workerInitialSlotValues[i]);
            vm.coolSlot(WORKER, bytes32(i));
        }

        vm.recordLogs();
        (bool success, bytes memory output) = TARGET.call{gas: GAS_LIMIT}(data);
        Vm.Gas memory gas = vm.lastCallGas();
        Vm.Log[] memory logs = vm.getRecordedLogs();

        uint256 commandLength = 43 + 4 * rootInitialSlotValues.length + 2 * rootCheckedSlots.length + 4
            * workerInitialSlotValues.length + 2 * workerCheckedSlots.length + 2 * logs.length;
        string[] memory command = new string[](commandLength);
        uint256 cursor = fillBaseCommand(
            command,
            name,
            type(MultiCallerParitySubject).runtimeCode,
            data,
            success,
            output,
            gas,
            0,
            TARGET.balance + WORKER.balance,
            TARGET.balance
        );

        command[cursor++] = "--account";
        command[cursor++] = string.concat(addressArg(WORKER), "=", hexString(type(WorkerParitySubject).runtimeCode));
        command[cursor++] = "--account";
        command[cursor++] = string.concat(addressArg(DELEGATE_LIB), "=", hexString(type(DelegateParityLib).runtimeCode));
        command[cursor++] = "--warm-address";
        command[cursor++] = addressArg(WORKER);
        command[cursor++] = "--warm-address";
        command[cursor++] = addressArg(DELEGATE_LIB);
        command[cursor++] = "--account-balance";
        command[cursor++] = string.concat(addressArg(WORKER), "=0");
        command[cursor++] = "--expect-account-balance";
        command[cursor++] = string.concat(addressArg(WORKER), "=", uintToString(WORKER.balance));

        for (uint256 i = 0; i < rootInitialSlotValues.length; i++) {
            command[cursor++] = "--storage";
            command[cursor++] = string.concat(wordHex(bytes32(i)), "=", wordHex(rootInitialSlotValues[i]));
            command[cursor++] = "--original-storage";
            command[cursor++] = string.concat(wordHex(bytes32(i)), "=", wordHex(bytes32(0)));
        }
        for (uint256 i = 0; i < rootCheckedSlots.length; i++) {
            bytes32 slot = rootCheckedSlots[i];
            command[cursor++] = "--expect-storage";
            command[cursor++] = string.concat(wordHex(slot), "=", wordHex(vm.load(TARGET, slot)));
        }
        for (uint256 i = 0; i < workerInitialSlotValues.length; i++) {
            command[cursor++] = "--account-storage";
            command[cursor++] =
                string.concat(addressArg(WORKER), ":", wordHex(bytes32(i)), "=", wordHex(workerInitialSlotValues[i]));
            command[cursor++] = "--account-original-storage";
            command[cursor++] = string.concat(addressArg(WORKER), ":", wordHex(bytes32(i)), "=", wordHex(bytes32(0)));
        }
        for (uint256 i = 0; i < workerCheckedSlots.length; i++) {
            bytes32 slot = workerCheckedSlots[i];
            command[cursor++] = "--expect-account-storage";
            command[cursor++] =
                string.concat(addressArg(WORKER), ":", wordHex(slot), "=", wordHex(vm.load(WORKER, slot)));
        }
        for (uint256 i = 0; i < logs.length; i++) {
            command[cursor++] = "--expect-log";
            command[cursor++] = logSpec(logs[i]);
        }

        vm.ffi(command);
    }

    function runDynamicCreateCase(DynamicCreateCase memory createCase) internal {
        vm.recordLogs();
        (bool success, bytes memory output) = TARGET.call{gas: GAS_LIMIT}(createCase.data);
        Vm.Gas memory gas = vm.lastCallGas();
        Vm.Log[] memory logs = vm.getRecordedLogs();

        uint256 commandLength = 45 + 2 * createCase.keccakAssignments.length + 2 * logs.length;
        string[] memory command = new string[](commandLength);

        BaseCommandCase memory base;
        base.name = createCase.name;
        base.code = type(CreateParityFactory).runtimeCode;
        base.data = createCase.data;
        base.success = success;
        base.output = output;
        base.gas = gas;
        base.callValue = 0;
        base.initialBalance = createCase.rootInitialBalance;
        base.expectedBalance = TARGET.balance;
        uint256 cursor = fillBaseCommandStruct(command, base);

        command[cursor++] = "--nonce";
        command[cursor++] = uintToString(createCase.rootNonce);
        command[cursor++] = "--expect-nonce";
        command[cursor++] = uintToString(vm.getNonce(TARGET));
        for (uint256 i = 0; i < createCase.keccakAssignments.length; i++) {
            command[cursor++] = "--keccak";
            command[cursor++] = createCase.keccakAssignments[i];
        }
        command[cursor++] = "--expect-storage";
        command[cursor++] = string.concat(wordHex(bytes32(uint256(0))), "=", wordHex(vm.load(TARGET, bytes32(0))));
        command[cursor++] = "--expect-storage";
        command[cursor++] =
            string.concat(wordHex(bytes32(uint256(1))), "=", wordHex(vm.load(TARGET, bytes32(uint256(1)))));
        command[cursor++] = "--expect-account-storage";
        command[cursor++] = string.concat(
            addressArg(createCase.expectedCreated),
            ":",
            wordHex(bytes32(0)),
            "=",
            wordHex(vm.load(createCase.expectedCreated, bytes32(0)))
        );
        command[cursor++] = "--expect-account-balance";
        command[cursor++] = string.concat(
            addressArg(createCase.expectedCreated), "=", uintToString(createCase.expectedCreated.balance)
        );
        command[cursor++] = "--expect-account-nonce";
        command[cursor++] = string.concat(
            addressArg(createCase.expectedCreated), "=", uintToString(vm.getNonce(createCase.expectedCreated))
        );
        for (uint256 i = 0; i < logs.length; i++) {
            command[cursor++] = "--expect-log";
            command[cursor++] = logSpec(logs[i]);
        }

        vm.ffi(command);
    }

    function fillBaseCommandStruct(string[] memory command, BaseCommandCase memory base)
        internal
        view
        returns (uint256 cursor)
    {
        command[0] = "python3";
        command[1] = "../../bin/evm_parity.py";
        command[2] = "check";
        command[3] = "--case";
        command[4] = base.name;
        command[5] = "--code";
        command[6] = hexString(base.code);
        command[7] = "--calldata";
        command[8] = hexString(base.data);
        command[9] = "--gas";
        command[10] = uintToString(GAS_LIMIT);
        command[11] = "--success";
        command[12] = base.success ? "1" : "0";
        command[13] = "--output";
        command[14] = hexString(base.output);
        command[15] = "--gas-used";
        command[16] = uintToString(base.gas.gasTotalUsed);
        command[17] = "--gas-remaining";
        command[18] = uintToString(base.gas.gasRemaining);
        command[19] = "--gas-refunded";
        command[20] = intToString(base.gas.gasRefunded);
        command[21] = "--caller";
        command[22] = hexString(abi.encodePacked(address(this)));
        command[23] = "--origin";
        command[24] = hexString(abi.encodePacked(tx.origin));
        command[25] = "--callvalue";
        command[26] = uintToString(base.callValue);
        command[27] = "--balance";
        command[28] = uintToString(base.initialBalance + base.callValue);
        command[29] = "--expect-balance";
        command[30] = uintToString(base.expectedBalance);
        return 31;
    }

    function fillBaseCommand(
        string[] memory command,
        string memory name,
        bytes memory code,
        bytes memory data,
        bool success,
        bytes memory output,
        Vm.Gas memory gas,
        uint256 callValue,
        uint256 initialBalance,
        uint256 expectedBalance
    ) internal view returns (uint256 cursor) {
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
        command[10] = uintToString(GAS_LIMIT);
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
        command[22] = hexString(abi.encodePacked(address(this)));
        command[23] = "--origin";
        command[24] = hexString(abi.encodePacked(tx.origin));
        command[25] = "--callvalue";
        command[26] = uintToString(callValue);
        command[27] = "--balance";
        command[28] = uintToString(initialBalance + callValue);
        command[29] = "--expect-balance";
        command[30] = uintToString(expectedBalance);
        return 31;
    }

    function installRuntime(bytes memory code) internal returns (address target) {
        vm.etch(TARGET, code);
        return TARGET;
    }

    function createAddressPreimage(address creator, uint256 nonce) internal pure returns (bytes memory) {
        if (nonce == 0) {
            return abi.encodePacked(bytes1(0xd6), bytes1(0x94), creator, bytes1(0x80));
        }
        require(nonce < 0x80, "nonce too large");
        return abi.encodePacked(bytes1(0xd6), bytes1(0x94), creator, bytes1(uint8(nonce)));
    }

    function create2AddressPreimage(address creator, bytes32 salt, bytes32 initHash)
        internal
        pure
        returns (bytes memory)
    {
        return abi.encodePacked(bytes1(0xff), creator, salt, initHash);
    }

    function keccakArg(bytes memory data, bytes32 hash) internal pure returns (string memory) {
        return string.concat(hexString(data), "=", wordHex(hash));
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

    function addressWordHex(address value) internal pure returns (string memory) {
        return wordHex(bytes32(uint256(uint160(value))));
    }

    function addressArg(address value) internal pure returns (string memory) {
        return hexString(abi.encodePacked(value));
    }

    function topicsHex(bytes32[] memory topics) internal pure returns (string memory) {
        if (topics.length == 0) return "";
        string memory out = wordHex(topics[0]);
        for (uint256 i = 1; i < topics.length; i++) {
            out = string.concat(out, ",", wordHex(topics[i]));
        }
        return out;
    }

    function logSpec(Vm.Log memory entry) internal pure returns (string memory) {
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
