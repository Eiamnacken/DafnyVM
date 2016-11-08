class   Stack{
	// values is a sequence of elements
	var values:seq<int>;

	
	//initialises the stack 
	constructor()
	modifies this;
	ensures |values| == 0
	{
		values:=[];
	}

	
	//removes the top element of the stack
	method pop()returns(value:int,fail:bool)
	modifies this
	ensures fail==>values==[] && old(|values|==0)
	ensures !fail ==> |values| == old(|values|-1)
	ensures !fail ==> old(values[0]) == value
	{	
		if(!isEmpty()){
			value:=values[0];
			if(|values|>=2){
				values:=values[1..];
			}else{values:=[];}
			fail:=false;
		}else{fail:=true;}
	}

	//puts an element on the top of the stack
	method push(variable: int)
	modifies this;
	ensures !isEmpty()
	ensures values[0]==variable;
	ensures |values| == old(|values|+1)
	{
		values:=[variable]+values;
	}

	//checks if the stack is empty
	function method isEmpty():bool
	reads this;
	{
		|values|==0
	}

	//duplicates the element which is on the top of the stack
	method dup()returns(fail:bool)
	modifies this
	ensures !fail==>moreThanTwo();
	ensures !fail==> values[0]==values[1];
	ensures !fail==>old(|values|>=1)
	ensures !fail==> values[0]==old(values[0])&&values[1]==old(values[0])
	ensures !fail ==> values[1..]==old(values)
	{
		if(!isEmpty()){
			values:= [values[0]]+values;
			fail:=false;
		}else{fail:=true;}
	}

	//checks if the stack has two or more elements
	function method moreThanTwo():bool
	reads this;
	{
		|values|>=2
	}

	//multiplicates the two elements which are on the top of stack
	method multi()returns(fail:bool)
	modifies this;
	ensures !fail==>!isEmpty()
	ensures !fail ==> old(|values|>=2)
	ensures fail==>old(|values|<2)
	ensures !fail==> values[0]==old(values[0]*values[1])
	ensures !fail==>values[1..]==old(values[2..])
	{
		if(moreThanTwo()){
			values:=[(values[0]*values[1])]+values[2..];
			fail:=false;
		}else{fail:=true;}
		
		
	}

	// adds the two elements which are on the top of the stack
	method add()returns(fail :bool)
	modifies this;
	ensures fail==>old(|values|<2)
	ensures !fail ==> old(|values|>=2)
	ensures !fail==>!isEmpty()
	ensures !fail==>values[0]==old(values[0]+values[1])
	ensures !fail==>values[1..]==old(values[2..])
	ensures fail==>values==old(values)
	{
		
		if(moreThanTwo()){
			values:=[(values[0]+values[1])]+values[2..];
			fail:=false;
		}else{fail:=true;}
		
	}

}

class {:autocontracts} Interpreter{
		var stack: Stack;

		constructor()
		modifies this
		{
			stack:= new Stack();
		}

		predicate Valid()
		reads this
		{
			stack != null
		}

		// if one of the operations failed, exitCode will be true
		method lexer(code : seq<int>)returns(exitCode:bool,returnValue:int)
		requires Valid()
		modifies this,stack
		requires code!=[]
		{
			exitCode:=false;
			var i := 0;
			while(i<|code|)
			invariant  i<|code|
			invariant Valid()
			modifies this,stack
			{
				//push
				if(code[i] == 0){
					stack.push(code[i+1]);
					if(i<|code|){
						i := i+1;
					}
				}
				//pop
				else if(code[i] == 1)
				{
					if(stack.isEmpty())
					{
						returnValue,exitCode:=stack.pop();
					}
				}
				//add
				else if(code[i] == 2)
				{
				if(stack.moreThanTwo())
				{
				  exitCode:=stack.add();
				  }
				}
				//multi 
				else if(code[i] == 3)
				{
					if(stack.moreThanTwo())
					{
						exitCode:=stack.multi();
					}
				}
				//dup 
				else if(code[i] == 4)
				{
					if(!stack.isEmpty())
					{
						exitCode:=stack.dup();
					}
				}
				if(i<|code|){
					i := i+1;
				}
			}
		}
}


// main method
method Main(){
	var interpreter: Interpreter := new Interpreter();
	var result:int;
	var exitCode:bool;
	exitCode,result:=interpreter.lexer([0,1,0,2,2]);

	
	print();
}

