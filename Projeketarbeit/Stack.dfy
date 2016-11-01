class   Stack{

	var values:seq<int>;

	

	constructor()
	modifies this;
	{
		values:=[];
	}

	

	method pop()returns(value:int,wasEmpty:bool)
	modifies this;
	ensures wasEmpty==>values==[]
	{	
		if(!isEmpty()){
			value:=values[0];
			if(|values|>=2){
				values:=values[1..];
			}else{
				values:=[];
			}
			wasEmpty:=false;
		}else{
			wasEmpty:=true;
		}
	}

	method push(variable: int)
	modifies this;
	ensures !isEmpty()
	ensures values[0]==variable;
	{
		values:=[variable]+values;
	}

	function method isEmpty():bool
	reads this;
	{
		|values|==0
	}

	method dup()returns()
	modifies this
	ensures !isEmpty()==>moreThanTwo();
	ensures !isEmpty()==> values[0]==values[1];
	{
		var dupValue:int;
		if(!isEmpty()){
			dupValue:=values[0];
			values:= [dupValue]+values;
		}
	}

	function method moreThanTwo():bool
	reads this;
	{
		|values|>=2
	}

	method multiFirstTwo()returns(value:int)
	modifies this;
	requires moreThanTwo()
	{
		var firstEmpty:bool;
		var secondEmpty:bool;
		var first:int;
		var second:int;
		first,firstEmpty:=pop();
		second,secondEmpty:=pop();
		if(!firstEmpty&&secondEmpty){
			value:=multi(first,second);
		}
		
		
	}

	method additFirstTwo()returns(value:int)
	modifies this;
	{
		var firstEmpty:bool;
		var secondEmpty:bool;
		var first:int;
		var second:int;
		first,firstEmpty:=pop();
		second,secondEmpty:=pop();
		if(!firstEmpty&&secondEmpty){
			value:=addit(first,second);
		}
		
	}

	method multi(first:int, second:int)returns(value:int)
	ensures value==first*second;
	{
		value:=first*second;
	}

	method addit(first:int,second:int)returns(value:int)
	ensures value==first+second
	{
		value:=first+second;
	}

}



method Main(){
	
	var stack:Stack := new Stack();
	var test:int;
	print(test);
	stack.push(5);
	stack.push(7);
	stack.push(4);
	stack.dup();
	var empty:bool;
	var emptyS:bool;
	var first:int;
	var second:int;
	first,empty:=stack.pop();
	second,emptyS:=stack.pop();
	if(!empty&&!emptyS){
		assert(first==second);
	}

	

	



}