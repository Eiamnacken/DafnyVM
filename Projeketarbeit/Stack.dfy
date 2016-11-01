class   Stack{

	var values:seq<int>;

	

	constructor()
	modifies this;
	{
		values:=[];
	}

	

	method pop()returns(value:int)
	modifies this;
	requires !isEmpty()
	{
			value:=values[0];
			values:=values[1..];
			return value;

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

	method dup()returns(value:bool)
	modifies this
	ensures !isEmpty()==>moreThanTwo();
	ensures !isEmpty()==> values[0]==values[1];
	{
		var dupValue:int;
		if(!isEmpty()){
			dupValue:=values[0];
			values:= [dupValue]+values;
			value:=true;
		}else{
			value:=false;
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
		var first:int;
		var second:int;
		first:=pop();

		if(!isEmpty()){
			second:=pop();
			value:=multi(first,second);
		}
		
	}

	method additFirstTwo()returns(value:int)
	modifies this;
	requires moreThanTwo()
	{
		var first:int;
		var second:int;
		first:=pop();
		if(!isEmpty()){
			second:=pop();
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