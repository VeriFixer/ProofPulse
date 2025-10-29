//:: Minimal case Reproducing something unexpected
method enterCarPark(n: int) returns (success: bool)
    ensures success == (n>0)
{
    if(n>0){
        return true;
    } else {
        return false;
    }
} //::    Unused by proof: if_sucess_bug.dfy(9,1)-(9,1): out-parameter 'success', which is subject to definite-assignment rules, is always initialized at this return point

 //:: Problem boogie adds a asssertions checking initialization in all function return points
 //:: In this case the function always enters or the if or the else and never executes code on botton
 //:: Truth be told I could considered this a warning as indeed the code can be simplified to this

//:: Still has same problem
 method enterCarPark2(n: int) returns (success: bool)
    ensures success == (n>0)
{
    if(n>0){
        return true;
    }
    return false;
} 


 method enterCarPark3(n: int) returns (success: bool)
    ensures success == (n>0)
{
    if(n>0){
        success := true;
    } else {
        success := false;
    }
} 

//:: Solution will treat this as a warning explaining why is happening