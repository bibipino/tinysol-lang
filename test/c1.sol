contract C1 {
    int x;
    bool b;
  
    function g() public { 
        if (b) x = x+1;
        else b=true;
    }

}
