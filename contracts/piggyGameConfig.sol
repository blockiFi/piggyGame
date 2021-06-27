// SPDX-License-Identifier: GPL-3.0

pragma solidity ^0.8.2;
import "https://github.com/OpenZeppelin/openzeppelin-contracts/blob/master/contracts/access/Ownable.sol";
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

contract piggyGame  is Ownable {
    // game pool fund (default 5%)
    uint16 public gamePoolFund = 5;
    // holders refletion (default 10%).
    uint16 public reflection = 10;
    //contract operation
    address _operator;
    //minimum amount allowed
    uint256 minAmount;
    
    
    //chances ranges from 1 - 1000 where 1 = 0.1 and 1000 == 10
    uint256 minChance = 1;
    uint256 maxChance =1000;
    
    //ease level 
    //degree of ease for prodition
    uint256 easelevel = 10;
    
    uint256 nonce;
    
    
    //test 
    uint256 public degree;
    
    uint256 public legendry;
    uint256 public userRoll;
    bool public success;
    uint256 public _chance;
    
    //piggy token interface 
    IBEP20 private _piggyToken;
    //game players structure
    enum boosterLevels {
        legendary,
        rare,
        common
    }
    struct chances {
        uint256 legendry;
        uint256 rare;
        uint256 common;
    }
    struct player {
        address playerAddress;
        boosterLevels playerBoosterLevels;
        chances playerChances;
        
    }
    //game players
    mapping(address => player) public players;
    //check if players is lengendary
    mapping(address => bool)  public isLengendary;
    //contains all lendary players to distribute reward easily
    address[]  public lengendaryHolders;

    
    
    
    //setup the piggyGame contract
    //@dev innitializes the owner and _operator
    //@_params piggyAddress is the address of the piggy token
    constructor(IBEP20 piggyAddress){
       _piggyToken  = piggyAddress ;
    
       _operator = msg.sender;
      
    }
    
   

   
    /**
     * @dev Throws if called by any account other than the operator.
     */
    modifier onlyOperator() {
        require(_operator == _msgSender(), "Ownable: caller is not the owner");
        _;
    }
     /**
     * @dev Returns the address of the current operator.
     */
    function operator() public view returns (address) {
        return _operator;
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
    //ajust the degree ease for getting lendendary
    function setEaseLevel(uint256 _easelevel) public {
        easelevel = _easelevel;
    }
    
    function play(uint256 amount)  public {
         require(_piggyToken.balanceOf(msg.sender) >= amount && amount > minAmount , "insuficient funds");
         //Transfer token to game contract
         _piggyToken.transferFrom(msg.sender, address(this), amount);
         //swap back and forth
         
         //roll base on amount of token insuficient
         
         //roll based on users default chances
         
         // check if common  > 10 increase chance by 1.1% then  reset common
         
         
         // check if rare  > 10 increase chance by 10% then  reset common
         
         // burn balance remaining
         
         
         
    }
    // this function rolls based on the amount of token burnt 
    function rollBaseOnTokenBurnt(uint256 amount) private {
        
    }
    // function roll(chances playerchances ) internal returns (enum){
       
       
    // }
    function attemptLegendary(uint256 chance) public  returns (bool) {
        
         // get degree of random ness
         _chance = chance;
        degree = getDegreeFromChance(chance);
        legendry = random(degree);
      
       userRoll = random(degree);
      if(userRoll == legendry){
          success = true;
          return true;
      }
       success = false;
         return false;
    }
    function attemptRare(uint256 chance) internal returns (bool) {
         
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
    function random(uint256 rdegree) internal  returns (uint256) {
    uint256 randomnumber = uint256(keccak256(abi.encodePacked(block.timestamp, msg.sender, nonce))) % degree;
    nonce++;
    return randomnumber;
}
    
    
}
    
    