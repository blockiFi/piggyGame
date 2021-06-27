
pragma solidity >=0.5.0;

interface IUniswapV2Factory {
    event PairCreated(address indexed token0, address indexed token1, address pair, uint);

    function feeTo() external view returns (address);
    function feeToSetter() external view returns (address);

    function getPair(address tokenA, address tokenB) external view returns (address pair);
    function allPairs(uint) external view returns (address pair);
    function allPairsLength() external view returns (uint);

    function createPair(address tokenA, address tokenB) external returns (address pair);

    function setFeeTo(address) external;
    function setFeeToSetter(address) external;
}

// File: @uniswap/v2-core/contracts/interfaces/IUniswapV2Pair.sol

pragma solidity >=0.5.0;

interface IUniswapV2Pair {
    event Approval(address indexed owner, address indexed spender, uint value);
    event Transfer(address indexed from, address indexed to, uint value);

    function name() external pure returns (string memory);
    function symbol() external pure returns (string memory);
    function decimals() external pure returns (uint8);
    function totalSupply() external view returns (uint);
    function balanceOf(address owner) external view returns (uint);
    function allowance(address owner, address spender) external view returns (uint);

    function approve(address spender, uint value) external returns (bool);
    function transfer(address to, uint value) external returns (bool);
    function transferFrom(address from, address to, uint value) external returns (bool);

    function DOMAIN_SEPARATOR() external view returns (bytes32);
    function PERMIT_TYPEHASH() external pure returns (bytes32);
    function nonces(address owner) external view returns (uint);

    function permit(address owner, address spender, uint value, uint deadline, uint8 v, bytes32 r, bytes32 s) external;

    event Mint(address indexed sender, uint amount0, uint amount1);
    event Burn(address indexed sender, uint amount0, uint amount1, address indexed to);
    event Swap(
        address indexed sender,
        uint amount0In,
        uint amount1In,
        uint amount0Out,
        uint amount1Out,
        address indexed to
    );
    event Sync(uint112 reserve0, uint112 reserve1);

    function MINIMUM_LIQUIDITY() external pure returns (uint);
    function factory() external view returns (address);
    function token0() external view returns (address);
    function token1() external view returns (address);
    function getReserves() external view returns (uint112 reserve0, uint112 reserve1, uint32 blockTimestampLast);
    function price0CumulativeLast() external view returns (uint);
    function price1CumulativeLast() external view returns (uint);
    function kLast() external view returns (uint);

    function mint(address to) external returns (uint liquidity);
    function burn(address to) external returns (uint amount0, uint amount1);
    function swap(uint amount0Out, uint amount1Out, address to, bytes calldata data) external;
    function skim(address to) external;
    function sync() external;

    function initialize(address, address) external;
}

// File: @uniswap/v2-periphery/contracts/interfaces/IUniswapV2Router01.sol

pragma solidity >=0.6.2;

interface IUniswapV2Router01 {
    function factory() external pure returns (address);
    function WETH() external pure returns (address);

    function addLiquidity(
        address tokenA,
        address tokenB,
        uint amountADesired,
        uint amountBDesired,
        uint amountAMin,
        uint amountBMin,
        address to,
        uint deadline
    ) external returns (uint amountA, uint amountB, uint liquidity);
    function addLiquidityETH(
        address token,
        uint amountTokenDesired,
        uint amountTokenMin,
        uint amountETHMin,
        address to,
        uint deadline
    ) external payable returns (uint amountToken, uint amountETH, uint liquidity);
    function removeLiquidity(
        address tokenA,
        address tokenB,
        uint liquidity,
        uint amountAMin,
        uint amountBMin,
        address to,
        uint deadline
    ) external returns (uint amountA, uint amountB);
    function removeLiquidityETH(
        address token,
        uint liquidity,
        uint amountTokenMin,
        uint amountETHMin,
        address to,
        uint deadline
    ) external returns (uint amountToken, uint amountETH);
    function removeLiquidityWithPermit(
        address tokenA,
        address tokenB,
        uint liquidity,
        uint amountAMin,
        uint amountBMin,
        address to,
        uint deadline,
        bool approveMax, uint8 v, bytes32 r, bytes32 s
    ) external returns (uint amountA, uint amountB);
    function removeLiquidityETHWithPermit(
        address token,
        uint liquidity,
        uint amountTokenMin,
        uint amountETHMin,
        address to,
        uint deadline,
        bool approveMax, uint8 v, bytes32 r, bytes32 s
    ) external returns (uint amountToken, uint amountETH);
    function swapExactTokensForTokens(
        uint amountIn,
        uint amountOutMin,
        address[] calldata path,
        address to,
        uint deadline
    ) external returns (uint[] memory amounts);
    function swapTokensForExactTokens(
        uint amountOut,
        uint amountInMax,
        address[] calldata path,
        address to,
        uint deadline
    ) external returns (uint[] memory amounts);
    function swapExactETHForTokens(uint amountOutMin, address[] calldata path, address to, uint deadline)
        external
        payable
        returns (uint[] memory amounts);
    function swapTokensForExactETH(uint amountOut, uint amountInMax, address[] calldata path, address to, uint deadline)
        external
        returns (uint[] memory amounts);
    function swapExactTokensForETH(uint amountIn, uint amountOutMin, address[] calldata path, address to, uint deadline)
        external
        returns (uint[] memory amounts);
    function swapETHForExactTokens(uint amountOut, address[] calldata path, address to, uint deadline)
        external
        payable
        returns (uint[] memory amounts);

    function quote(uint amountA, uint reserveA, uint reserveB) external pure returns (uint amountB);
    function getAmountOut(uint amountIn, uint reserveIn, uint reserveOut) external pure returns (uint amountOut);
    function getAmountIn(uint amountOut, uint reserveIn, uint reserveOut) external pure returns (uint amountIn);
    function getAmountsOut(uint amountIn, address[] calldata path) external view returns (uint[] memory amounts);
    function getAmountsIn(uint amountOut, address[] calldata path) external view returns (uint[] memory amounts);
}

// File: @uniswap/v2-periphery/contracts/interfaces/IUniswapV2Router02.sol

pragma solidity >=0.6.2;


interface IUniswapV2Router02 is IUniswapV2Router01 {
    function removeLiquidityETHSupportingFeeOnTransferTokens(
        address token,
        uint liquidity,
        uint amountTokenMin,
        uint amountETHMin,
        address to,
        uint deadline
    ) external returns (uint amountETH);
    function removeLiquidityETHWithPermitSupportingFeeOnTransferTokens(
        address token,
        uint liquidity,
        uint amountTokenMin,
        uint amountETHMin,
        address to,
        uint deadline,
        bool approveMax, uint8 v, bytes32 r, bytes32 s
    ) external returns (uint amountETH);

    function swapExactTokensForTokensSupportingFeeOnTransferTokens(
        uint amountIn,
        uint amountOutMin,
        address[] calldata path,
        address to,
        uint deadline
    ) external;
    function swapExactETHForTokensSupportingFeeOnTransferTokens(
        uint amountOutMin,
        address[] calldata path,
        address to,
        uint deadline
    ) external payable;
    function swapExactTokensForETHSupportingFeeOnTransferTokens(
        uint amountIn,
        uint amountOutMin,
        address[] calldata path,
        address to,
        uint deadline
    ) external;
}

pragma solidity ^0.8.0;

/**
 * @dev Collection of functions related to the address type
 */
library Address {
    /**
     * @dev Returns true if `account` is a contract.
     *
     * [IMPORTANT]
     * ====
     * It is unsafe to assume that an address for which this function returns
     * false is an externally-owned account (EOA) and not a contract.
     *
     * Among others, `isContract` will return false for the following
     * types of addresses:
     *
     *  - an externally-owned account
     *  - a contract in construction
     *  - an address where a contract will be created
     *  - an address where a contract lived, but was destroyed
     * ====
     */
    function isContract(address account) internal view returns (bool) {
        // This method relies on extcodesize, which returns 0 for contracts in
        // construction, since the code is only stored at the end of the
        // constructor execution.

        uint256 size;
        assembly {
            size := extcodesize(account)
        }
        return size > 0;
    }

    /**
     * @dev Replacement for Solidity's `transfer`: sends `amount` wei to
     * `recipient`, forwarding all available gas and reverting on errors.
     *
     * https://eips.ethereum.org/EIPS/eip-1884[EIP1884] increases the gas cost
     * of certain opcodes, possibly making contracts go over the 2300 gas limit
     * imposed by `transfer`, making them unable to receive funds via
     * `transfer`. {sendValue} removes this limitation.
     *
     * https://diligence.consensys.net/posts/2019/09/stop-using-soliditys-transfer-now/[Learn more].
     *
     * IMPORTANT: because control is transferred to `recipient`, care must be
     * taken to not create reentrancy vulnerabilities. Consider using
     * {ReentrancyGuard} or the
     * https://solidity.readthedocs.io/en/v0.5.11/security-considerations.html#use-the-checks-effects-interactions-pattern[checks-effects-interactions pattern].
     */
    function sendValue(address payable recipient, uint256 amount) internal {
        require(address(this).balance >= amount, "Address: insufficient balance");

        (bool success, ) = recipient.call{value: amount}("");
        require(success, "Address: unable to send value, recipient may have reverted");
    }

    /**
     * @dev Performs a Solidity function call using a low level `call`. A
     * plain `call` is an unsafe replacement for a function call: use this
     * function instead.
     *
     * If `target` reverts with a revert reason, it is bubbled up by this
     * function (like regular Solidity function calls).
     *
     * Returns the raw returned data. To convert to the expected return value,
     * use https://solidity.readthedocs.io/en/latest/units-and-global-variables.html?highlight=abi.decode#abi-encoding-and-decoding-functions[`abi.decode`].
     *
     * Requirements:
     *
     * - `target` must be a contract.
     * - calling `target` with `data` must not revert.
     *
     * _Available since v3.1._
     */
    function functionCall(address target, bytes memory data) internal returns (bytes memory) {
        return functionCall(target, data, "Address: low-level call failed");
    }

    /**
     * @dev Same as {xref-Address-functionCall-address-bytes-}[`functionCall`], but with
     * `errorMessage` as a fallback revert reason when `target` reverts.
     *
     * _Available since v3.1._
     */
    function functionCall(
        address target,
        bytes memory data,
        string memory errorMessage
    ) internal returns (bytes memory) {
        return functionCallWithValue(target, data, 0, errorMessage);
    }

    /**
     * @dev Same as {xref-Address-functionCall-address-bytes-}[`functionCall`],
     * but also transferring `value` wei to `target`.
     *
     * Requirements:
     *
     * - the calling contract must have an ETH balance of at least `value`.
     * - the called Solidity function must be `payable`.
     *
     * _Available since v3.1._
     */
    function functionCallWithValue(
        address target,
        bytes memory data,
        uint256 value
    ) internal returns (bytes memory) {
        return functionCallWithValue(target, data, value, "Address: low-level call with value failed");
    }

    /**
     * @dev Same as {xref-Address-functionCallWithValue-address-bytes-uint256-}[`functionCallWithValue`], but
     * with `errorMessage` as a fallback revert reason when `target` reverts.
     *
     * _Available since v3.1._
     */
    function functionCallWithValue(
        address target,
        bytes memory data,
        uint256 value,
        string memory errorMessage
    ) internal returns (bytes memory) {
        require(address(this).balance >= value, "Address: insufficient balance for call");
        require(isContract(target), "Address: call to non-contract");

        (bool success, bytes memory returndata) = target.call{value: value}(data);
        return _verifyCallResult(success, returndata, errorMessage);
    }

    /**
     * @dev Same as {xref-Address-functionCall-address-bytes-}[`functionCall`],
     * but performing a static call.
     *
     * _Available since v3.3._
     */
    function functionStaticCall(address target, bytes memory data) internal view returns (bytes memory) {
        return functionStaticCall(target, data, "Address: low-level static call failed");
    }

    /**
     * @dev Same as {xref-Address-functionCall-address-bytes-string-}[`functionCall`],
     * but performing a static call.
     *
     * _Available since v3.3._
     */
    function functionStaticCall(
        address target,
        bytes memory data,
        string memory errorMessage
    ) internal view returns (bytes memory) {
        require(isContract(target), "Address: static call to non-contract");

        (bool success, bytes memory returndata) = target.staticcall(data);
        return _verifyCallResult(success, returndata, errorMessage);
    }

    /**
     * @dev Same as {xref-Address-functionCall-address-bytes-}[`functionCall`],
     * but performing a delegate call.
     *
     * _Available since v3.4._
     */
    function functionDelegateCall(address target, bytes memory data) internal returns (bytes memory) {
        return functionDelegateCall(target, data, "Address: low-level delegate call failed");
    }

    /**
     * @dev Same as {xref-Address-functionCall-address-bytes-string-}[`functionCall`],
     * but performing a delegate call.
     *
     * _Available since v3.4._
     */
    function functionDelegateCall(
        address target,
        bytes memory data,
        string memory errorMessage
    ) internal returns (bytes memory) {
        require(isContract(target), "Address: delegate call to non-contract");

        (bool success, bytes memory returndata) = target.delegatecall(data);
        return _verifyCallResult(success, returndata, errorMessage);
    }

    function _verifyCallResult(
        bool success,
        bytes memory returndata,
        string memory errorMessage
    ) private pure returns (bytes memory) {
        if (success) {
            return returndata;
        } else {
            // Look for revert reason and bubble it up if present
            if (returndata.length > 0) {
                // The easiest way to bubble the revert reason is using memory via assembly

                assembly {
                    let returndata_size := mload(returndata)
                    revert(add(32, returndata), returndata_size)
                }
            } else {
                revert(errorMessage);
            }
        }
    }
}
interface IBEP20 {
    function burn(uint256 amount) external  returns (bool);
    /**
     * @dev Returns the amount of tokens in existence.
     */
    function totalSupply() external view returns (uint256);

    /**
     * @dev Returns the amount of tokens owned by `account`.
     */
    function balanceOf(address account) external view returns (uint256);

    /**
     * @dev Moves `amount` tokens from the caller's account to `recipient`.
     *
     * Returns a boolean value indicating whether the operation succeeded.
     *
     * Emits a {Transfer} event.
     */
    function transfer(address recipient, uint256 amount) external returns (bool);

    /**
     * @dev Returns the remaining number of tokens that `spender` will be
     * allowed to spend on behalf of `owner` through {transferFrom}. This is
     * zero by default.
     *
     * This value changes when {approve} or {transferFrom} are called.
     */
    function allowance(address owner, address spender) external view returns (uint256);

    /**
     * @dev Sets `amount` as the allowance of `spender` over the caller's tokens.
     *
     * Returns a boolean value indicating whether the operation succeeded.
     *
     * IMPORTANT: Beware that changing an allowance with this method brings the risk
     * that someone may use both the old and the new allowance by unfortunate
     * transaction ordering. One possible solution to mitigate this race
     * condition is to first reduce the spender's allowance to 0 and set the
     * desired value afterwards:
     * https://github.com/ethereum/EIPs/issues/20#issuecomment-263524729
     *
     * Emits an {Approval} event.
     */
    function approve(address spender, uint256 amount) external returns (bool);

    /**
     * @dev Moves `amount` tokens from `sender` to `recipient` using the
     * allowance mechanism. `amount` is then deducted from the caller's
     * allowance.
     *
     * Returns a boolean value indicating whether the operation succeeded.
     *
     * Emits a {Transfer} event.
     */
    function transferFrom(
        address sender,
        address recipient,
        uint256 amount
    ) external returns (bool);

    /**
     * @dev Emitted when `value` tokens are moved from one account (`from`) to
     * another (`to`).
     *
     * Note that `value` may be zero.
     */
    event Transfer(address indexed from, address indexed to, uint256 value);

    /**
     * @dev Emitted when the allowance of a `spender` for an `owner` is set by
     * a call to {approve}. `value` is the new allowance.
     */
    event Approval(address indexed owner, address indexed spender, uint256 value);
}


pragma solidity ^0.8.0;

import "../utils/Context.sol";

/**
 * @dev Contract module which provides a basic access control mechanism, where
 * there is an account (an owner) that can be granted exclusive access to
 * specific functions.
 *
 * By default, the owner account will be the one that deploys the contract. This
 * can later be changed with {transferOwnership}.
 *
 * This module is used through inheritance. It will make available the modifier
 * `onlyOwner`, which can be applied to your functions to restrict their use to
 * the owner.
 */
abstract contract Ownable is Context {
    address private _owner;

    event OwnershipTransferred(address indexed previousOwner, address indexed newOwner);

    /**
     * @dev Initializes the contract setting the deployer as the initial owner.
     */
    constructor() {
        _setOwner(_msgSender());
    }

    /**
     * @dev Returns the address of the current owner.
     */
    function owner() public view virtual returns (address) {
        return _owner;
    }

    /**
     * @dev Throws if called by any account other than the owner.
     */
    modifier onlyOwner() {
        require(owner() == _msgSender(), "Ownable: caller is not the owner");
        _;
    }

    /**
     * @dev Leaves the contract without owner. It will not be possible to call
     * `onlyOwner` functions anymore. Can only be called by the current owner.
     *
     * NOTE: Renouncing ownership will leave the contract without an owner,
     * thereby removing any functionality that is only available to the owner.
     */
    function renounceOwnership() public virtual onlyOwner {
        _setOwner(address(0));
    }

    /**
     * @dev Transfers ownership of the contract to a new account (`newOwner`).
     * Can only be called by the current owner.
     */
    function transferOwnership(address newOwner) public virtual onlyOwner {
        require(newOwner != address(0), "Ownable: new owner is the zero address");
        _setOwner(newOwner);
    }

    function _setOwner(address newOwner) private {
        address oldOwner = _owner;
        _owner = newOwner;
        emit OwnershipTransferred(oldOwner, newOwner);
    }
}


// SPDX-License-Identifier: GPL-3.0

pragma solidity ^0.8.2;

contract piggyGame  is Ownable {
    using Address for address;
    // game pool fund (default 5%)
    uint16 public gamePoolFund = 5;
    address gamePoolFundAddress;
    // holders refletion (default 10%).
    uint16 public reflection = 10;
    uint16 public reflectionAddress;
    //contract operation
    address  public _operator;
   
    
    // token burn grade 
    uint256  public commonGrade = 1000000 ether;
    uint256 public  rareGrade = 10000000 ether;
    uint256 public legendaryGrade = 100000000 ether; 
    
    
    // chances per grade
   uint256  public commonGradeChance = 2;
    uint256 public rareGradeChance = 300;
    uint256 public legendaryGradeChance = 500;
    
    
    //chances ranges from 1 - 1000 where 1 = 0.1 and 1000 == 10
    uint256  public minChance = 1;
    uint256  public maxChance =1000;
    
    //ease level 
    //degree of ease for prodition
    uint256  easelevel = 40;
    
    
    //boost burn threshold / rate 
    
    uint256  public commonBurnTreshold = 10;
    uint256 public rareBurnTreshold = 10;

    uint256   commonBurnRate = 11;
    uint256   rareBurnRate = 120;
    
    
    
    uint256 nonce;
    
    
    // The swap router, modifiable. Will be changed to TestSwap's router when our own AMM release
    IUniswapV2Router02 public testSwapRouter;
    // The trading pair
    address public testSwapPair;
    
    //piggy token interface 
    IBEP20 private _piggyToken;
    address public piggyAddress;
    //game players structure
    struct boosterLevels {
     uint256   legendary;
     uint256   rare;
     uint256   common;
    }
    struct chances {
        uint256 legendary;
        uint256 rare;
        uint256 common;
    }
    struct player {
        address playerAddress;
        boosterLevels playerBoosterLevels;
        uint256 gamePlayed;
        uint256 rewardsEarned;
       
        
    }
    //game players
    mapping(address => player) public players;
    //check if players is lengendary
    mapping(address => bool) public isLengendary;
    //contains all lendary players to distribute reward easily
    address[] public lengendaryHolders;
    
     chances public defaultChances;
     
    //setup the piggyGame contract
    //@dev innitializes the owner and _operator
    //@_params piggyAddress is the address of the piggy token
    constructor(IBEP20 piggyToken){
       _piggyToken = piggyToken ;
       _operator = msg.sender;
      
    }
    
   

   
    /**
     * @dev Throws if called by any account other than the operator.
     */
    modifier onlyOperator() {
        require( _operator == _msgSender() || owner() == _msgSender(), "Ownable: caller is not the owner");
        _;
    }
    
    //event
     event TestSwapRouterUpdated(address indexed operator, address indexed router, address indexed pair);
     /**
     * @dev Returns the address of the current operator.
     */
    function operator() public view returns (address) {
        return _operator;
    }
    function setGamePoolFundAddress(address _gamePoolFundAddress) public onlyOperator {
        gamePoolFundAddress  = _gamePoolFundAddress;
    }
    function setReflectionFundAddress(address _reflectionAddress) public onlyOperator {
        reflectionAddress  = _reflectionAddress;
    }
     /**
     * @dev Transfers ownership of the contract to a new account (`newOwner`).
     * Can only be called by the current owner.
     */
    function transferOperator(address newOperator) public  onlyOperator {
        require(newOperator != address(0), " new operator is the zero address");
        // emit OperatorTransferred(_operator, newOperator);
        _operator = newOperator;
    }
    // adjust the minumun amount to burn
    function AdjustBurnMinimums(uint256 common_min , uint256 rare_min , uint legendary_min) public onlyOperator{
        commonGrade = common_min;
        rareGrade = rare_min;
        legendaryGrade = legendary_min; 
    }
    // @dev  modify ease level ranges from 10 - 100;
    // @_param easelevel
     function setEaseLevel(uint256 _easelevel) public onlyOperator{
         require(_easelevel > 10 && _easelevel < 200 , "Ease level out of range");
            easelevel = _easelevel;
    }
    // adjusting the default chances of getting a common a rar and a lengendary
    //@_param_common chances for common
    //@_param_rare chances for rare
    //@_param_legendary chances for legendary
    function setDefaultChances(uint256 common  , uint256 rare , uint256 legendary ) public onlyOperator {
        require(
             common <=1000 &&
             rare <=1000 &&
             legendary <=1000 && ,
             "Invalid parameter set range should be less<= 1000"
             );
             defaultChances.legendary = legendary;
             defaultChances.rare = rare;
             defaultChances.common = common;
        
    }
    //set booster burn threshold and rate
    // burn threshold is the minimun of booster the can be burnt for an increase in chance of getting legendary;
    // burn rate is the value increase in chance for each burn.
    function setDefaultChances(uint256 _commonBurnTreshold  , uint256 _commonBurnRate ,uint256 _rareBurnTreshold, uint256 _rareBurnRate ) public onlyOperator {
      
             commonBurnTreshold = _commonBurnTreshold;
             commonBurnRate = _commonBurnRate;
             rareBurnTreshold = _rareBurnTreshold;
             rareBurnRate = _rareBurnRate;
    }
    function play(uint256 amount)  public  {
        uint256 tokenbalance =_piggyToken.balanceOf(msg.sender);
         require( tokenbalance >= amount && amount >= commonGrade , "insuficient funds");
         
         //Transfer token to piggyGame contract
        _piggyToken.transferFrom(msg.sender, address(this), amount);
        
         
         
        //Transfer to gamePoolFund default 5% 
        uint256 gamePoolFundAmount = (amount * gamePoolFund /100);
        uint256 reflectionAmount  = (amount * reflection / 100);
        uint256 balance = (amount - (gamePoolFundAmount + reflectionAmount));
        // send to gamefund
        _piggyToken.transfer(gamePoolFundAddress , gamePoolFundAmount);
        // reflect to users
        _piggyToken.transfer(gamePoolFundAddress ,   reflectionAmount); 
        
        
         // capture innitial Eth balance
         uint256 innitialEthBalance = address(this).balance;
         
         //swap back and forth
         swapTokensForEth(balance);
         
         // capture  Eth balance After
         uint256 afterEthBalance = address(this).balance;
         

         require(afterEthBalance > innitialEthBalance , "Nagative Swap occured");
         // capture  Eth received
         uint256 EthRecieved = afterEthBalance - innitialEthBalance;
         
         //SwapEthForToken
         swapEthForTokens(EthRecieved);
         
         //burn remaining tokens;
         //roll base on amount of token supply 
         bool getreward = canGetReward(amount);
         if(getreward){ 
            getReward(); 
         }
         
         
        // update Player gameplay Count
         
       player storage currentPlayer = players[msg.sender];
         currentPlayer.gamePlayed += 1;  
         
    }
    function getReward() internal returns(bool){
      chances storage playchance =  defaultChances;
      player storage currentPlayer = players[msg.sender];
      currentPlayer.rewardsEarned += 1;
      //burn common treshhold for more legendary chance
      if(currentPlayer.playerBoosterLevels.common >= commonBurnTreshold){
          playchance.legendary += commonBurnRate;
          currentPlayer.playerBoosterLevels.common = 0;
          
          
      }
      
      if(currentPlayer.playerBoosterLevels.rare >= rareBurnTreshold){
           playchance.legendary += rareBurnRate;
           currentPlayer.playerBoosterLevels.rare = 0;
      }
      
      // atempt legendary
      
      if(attemptRoll(playchance.legendary)){
          currentPlayer.playerBoosterLevels.legendary += 1;
          if(!isLengendary[msg.sender]){
              isLengendary[msg.sender] = true;
              lengendaryHolders.push(msg.sender);
          }
          return true;
          
      }
      if(attemptRoll(playchance.rare)){
           currentPlayer.playerBoosterLevels.rare += 1;
           return true;
      }
      currentPlayer.playerBoosterLevels.common += 1;
      
      
    }
    // this function rolls based on the amount of token burnt 
    function canGetReward(uint256 amount ) internal returns(bool)  {
        if(amount < rareGrade ){
            return attemptRoll(commonGradeChance);
        }else  if(amount < legendaryGrade){
            return attemptRoll(rareGradeChance);
        }else {
            return attemptRoll(legendaryGradeChance);
        }
        
    }
    
    function attemptRoll(uint256 chance) public  returns (bool) {
        
         // get degree of random ness
      uint256  degree = getDegreeFromChance(chance);
      uint256  target = random(degree);
      
      uint256 userRoll = random(degree);
      if(userRoll == target){
          return true;
      }
         return false;
    }
    
    function getDegreeFromChance(uint chance ) internal returns (uint256 ){
        require(chance <= maxChance , "Invalid chance value");
        if(((maxChance - chance) <= 0) && (chance <= maxChance)){
            return maxChance/10;
        }
       else if(maxChance - chance >= easelevel){
           return (maxChance - chance) / easelevel; 
        }
        return maxChance - chance;
    }
    function random(uint256 rdegree) internal returns (uint256) {
    uint256 randomnumber = uint256(keccak256(abi.encodePacked(block.timestamp, msg.sender, nonce))) % rdegree;
    nonce++;
    return randomnumber;
}
 // To receive BNB from testSwapRouter when swapping
    receive() external payable {}
 /**
     * @dev Update the swap router.
     * Can only be called by the current operator.
     */
    function updateTestSwapRouter(address _router , address _piggyAddress ) public onlyOperator {
        piggyAddress = _piggyAddress;
        testSwapRouter = IUniswapV2Router02(_router);
        testSwapPair = IUniswapV2Factory(testSwapRouter.factory()).getPair(_piggyAddress , testSwapRouter.WETH());
        require(testSwapPair != address(0), "TEST::updateTestSwapRouter: Invalid pair address.");
        emit TestSwapRouterUpdated(msg.sender, address(testSwapRouter), testSwapPair);
    }   
    /// @dev Swap tokens for eth
    function swapTokensForEth(uint256 tokenAmount ) private {
        // generate the testSwap pair path of token -> weth
        address[] memory path = new address[](2);
        path[0] = piggyAddress;
        path[1] = testSwapRouter.WETH();

        _piggyToken.approve(address(testSwapRouter), tokenAmount);
        // uint256 AmountsOut  =  testSwapRouter.getAmountsOut( tokenAmount , path );
        
        // uint256 feesAndChurn = AmountsOut - (AmountsOut * 35 / 100);
        // uint256 amountIn = AmountsOut - feesAndChurn;
        // make the swap
        testSwapRouter.swapExactTokensForETHSupportingFeeOnTransferTokens(
           tokenAmount ,
            0, // 35% less eth for fees and churn
            path,
             address(this),
            block.timestamp
        );
    }
    // @dev Swap tokens for eth
    function swapEthForTokens(uint256 EthAmount ) private {
        // generate the testSwap pair path of token -> weth
        address[] memory path = new address[](2);
        path[0] = testSwapRouter.WETH();
        path[1] = piggyAddress;

        
        // uint256 AmountsOut  =  testSwapRouter.getAmountsOut(EthAmount , path );
        
        // uint256 feesAndChurn = AmountsOut - (AmountsOut * 35 / 100);
        // uint256 amountIn = AmountsOut - feesAndChurn;
        // make the swap
        testSwapRouter.swapExactETHForTokensSupportingFeeOnTransferTokens{value: EthAmount}(
           0 ,// 35% less token for fees and churn 
            path,
             address(this),
            block.timestamp
        );
    }
    
}
    
    