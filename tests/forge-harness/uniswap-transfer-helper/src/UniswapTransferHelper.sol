// SPDX-License-Identifier: GPL-2.0-or-later
pragma solidity ^0.8.20;

// Adapted from Uniswap v3-periphery v1.3.0 TransferHelper, with the IERC20
// import inlined because the source-semantics harness intentionally excludes
// import resolution.
interface IERC20 {
    function transfer(address recipient, uint256 amount)
        external
        returns (bool);

    function approve(address spender, uint256 amount)
        external
        returns (bool);

    function transferFrom(address sender, address recipient, uint256 amount)
        external
        returns (bool);
}

library TransferHelper {
    function safeTransferFrom(
        address token,
        address from,
        address to,
        uint256 value
    ) internal {
        (bool success, bytes memory data) =
            token.call(
                abi.encodeWithSelector(
                    IERC20.transferFrom.selector,
                    from,
                    to,
                    value
                )
            );
        require(
            success && (data.length == 0 || abi.decode(data, (bool))),
            "STF"
        );
    }

    function safeTransfer(
        address token,
        address to,
        uint256 value
    ) internal {
        (bool success, bytes memory data) =
            token.call(
                abi.encodeWithSelector(IERC20.transfer.selector, to, value)
            );
        require(
            success && (data.length == 0 || abi.decode(data, (bool))),
            "ST"
        );
    }

    function safeApprove(
        address token,
        address to,
        uint256 value
    ) internal {
        (bool success, bytes memory data) =
            token.call(
                abi.encodeWithSelector(IERC20.approve.selector, to, value)
            );
        require(
            success && (data.length == 0 || abi.decode(data, (bool))),
            "SA"
        );
    }

    function safeTransferETH(address to, uint256 value) internal {
        (bool success, ) = to.call{value: value}(new bytes(0));
        require(success, "STE");
    }
}

contract UniswapTransferHelperHarness {
    function pull(
        address token,
        address from,
        address to,
        uint256 value
    ) external {
        TransferHelper.safeTransferFrom(token, from, to, value);
    }

    function push(address token, address to, uint256 value) external {
        TransferHelper.safeTransfer(token, to, value);
    }

    function approve(address token, address to, uint256 value) external {
        TransferHelper.safeApprove(token, to, value);
    }

    function pay(address payable to, uint256 value) external payable {
        TransferHelper.safeTransferETH(to, value);
    }

    receive() external payable {}
}

contract UniswapTransferHelperReturnTrueToken {
    address public lastFrom;
    address public lastTo;
    address public lastSpender;
    uint256 public lastValue;

    function transferFrom(address from, address to, uint256 value)
        external
        returns (bool)
    {
        lastFrom = from;
        lastTo = to;
        lastValue = value;
        return true;
    }

    function transfer(address to, uint256 value) external returns (bool) {
        lastTo = to;
        lastValue = value;
        return true;
    }

    function approve(address spender, uint256 value)
        external
        returns (bool)
    {
        lastSpender = spender;
        lastValue = value;
        return true;
    }
}

contract UniswapTransferHelperReturnFalseToken {
    function transferFrom(address, address, uint256)
        external
        pure
        returns (bool)
    {
        return false;
    }

    function transfer(address, uint256) external pure returns (bool) {
        return false;
    }

    function approve(address, uint256) external pure returns (bool) {
        return false;
    }
}

contract UniswapTransferHelperNoReturnToken {
    address public lastFrom;
    address public lastTo;
    address public lastSpender;
    uint256 public lastValue;

    function transferFrom(address from, address to, uint256 value) external {
        lastFrom = from;
        lastTo = to;
        lastValue = value;
    }

    function transfer(address to, uint256 value) external {
        lastTo = to;
        lastValue = value;
    }

    function approve(address spender, uint256 value) external {
        lastSpender = spender;
        lastValue = value;
    }
}

contract UniswapTransferHelperEthRecipient {
    uint256 public received;

    receive() external payable {
        received += msg.value;
    }
}

contract UniswapTransferHelperRejectEth {
    receive() external payable {
        revert("reject");
    }
}
