package asign3;
import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.FileNotFoundException;
import java.io.FileReader;
import java.io.FileWriter;
import java.io.IOException;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;

public class inference {

	Map<String, List<String>> KB = new HashMap<>();
	static BufferedWriter output_file =null ;
	List<String> loopDetectionList= new ArrayList<>();
	static int var=0;
	public static void main(String[] args) 
	{
		
		try 
		{
			output_file=new BufferedWriter(new FileWriter("output.txt"));
		} catch (IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		inference inf = new inference();
		
		BufferedReader input_buff;
		List<String> query_list = new ArrayList<>();
		try 
		{
			input_buff = new BufferedReader(new FileReader(args[1]));
			int query_cnt = Integer.parseInt(input_buff.readLine());

			for (int i = 0; i < query_cnt; i++) 
			{
				query_list.add(input_buff.readLine());
			}

			int KB_cnt = Integer.parseInt(input_buff.readLine());

			for (int i = 0; i < KB_cnt; i++)
			{
				inf.add_sentence(input_buff.readLine());
			}

			inf.print_KB();

			for (int i = 0; i < query_cnt; i++)
			{
				inf.loopDetectionList= new ArrayList<>();
				var=0;
				inf.solve(query_list.get(i));
			}
			
			output_file.close();
		} 
		catch (NumberFormatException e)
		{
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		catch (FileNotFoundException e)
		{
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		catch (Exception e)
		{
			// TODO Auto-generated catch block
			e.printStackTrace();
		}

	}
	private String standardize(String clause)
	{
		String list[]=clause.split(" => ");
		int flag1=0;
		int flag2=0;
		if(list.length==1)
		{
			return list[0];
		}
		else
		{//LHS
			String LHS[]=list[0].split("\\^");
			String finalclause="";	
			for(int i=0;i<LHS.length;i++)
			{
				LHS[i]=LHS[i].trim();
				String subst= LHS[i].substring(LHS[i].indexOf("(")+1, LHS[i].indexOf(")"));
				String[] args= subst.split(",");
				String newstr="";
				
				for(int j=0;j<args.length;j++)
				{
					System.out.println("args[j]="+args[j]);
					if(isVar(args[j]))
					{
						System.out.println("is var");
						args[j]+=var+",";
						flag1=1;
						System.out.println("args[j]="+args[j]);
					}
					else
						args[j]=args[j]+",";
					
					System.out.println("args[j]="+args[j]);
					newstr+=args[j];
				}
				System.out.println("newstr"+newstr);
				if(newstr.charAt(newstr.length()-1)==',')
				newstr=newstr.substring(0, newstr.length()-1);
				System.out.println("newstr: "+newstr);
				finalclause+=getPredicate(LHS[i])+"("+newstr+")"+" ^ ";
			}
			finalclause=finalclause.substring(0, finalclause.length()-3);
			finalclause=finalclause.concat(" => ");
			
			//rhs
			String rhs=list[1].substring(list[1].indexOf("(")+1,list[1].indexOf(")"));
			String args[]=rhs.split(",");
			String newstr="";
			
			for(int j=0;j<args.length;j++)
			{
				if(isVar(args[j]))
				{
					args[j]+=var+",";
					flag2=1;
				}
				else
					args[j]=args[j]+",";
				
				newstr+=args[j];
			}
			if(newstr.charAt(newstr.length()-1)==',')
			newstr=newstr.substring(0,newstr.length()-1);
			finalclause+=getPredicate(list[1])+"("+newstr+")";
			System.out.println(finalclause);
			var++;
			return finalclause;
		}//else
		
	}

	private void solve(String string) {
		
		List<String> goals = new ArrayList<>();
		goals.add(string);
		List<Map<String, String>> subs = Backward_chaining(goals, new HashMap<String, String>());
		System.out.println("------------------------------------------------------------------------");
		if (subs.isEmpty()) {
			System.out.println("FALSE");
			try {
				output_file.write("FALSE\r\n");
			} catch (IOException e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			}
		} else {
			
			for(Map<String,String>maps:subs)
			{
				for(Entry<String, String>entry: maps.entrySet())
				{
					System.out.println("key::"+entry.getKey()+" value::"+entry.getValue());
				}
			}
			System.out.println("TRUE");
			try {
				output_file.write("TRUE\r\n");
			} catch (IOException e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			}
		}
		
	}

	private List<Map<String, String>> Backward_chaining(List<String> goals, Map<String, String> substi) {
		List<Map<String, String>> answer = new ArrayList<>();

		if (goals.isEmpty()) {
			answer.add(substi);
			return answer;
		}
		
		
		String subgoal = goals.remove(0);
		
		subgoal = substitute(subgoal, substi);

		if(loopDetectionList.contains(subgoal))
			return answer;
		else if(compare_with_goals(subgoal))
		{
			return answer;
		}
		String copy_subgoal=subgoal;
		String goalPredicate = getPredicate(subgoal);

		List<String> matching_rules = KB.get(goalPredicate);
		List<String> new_matching_rules = KB.get(goalPredicate);
		subgoal = subgoal.substring(subgoal.indexOf("(") + 1, subgoal.indexOf(")"));

		if(matching_rules==null)
		{
			return answer;
		}
		String q;
		for (String s : matching_rules) {
			s=standardize(s);
			String list[] = s.split(" => ");
			if (list.length == 1) {
				q = s;
			} else {
				q = list[1];
			}
			q = q.substring(q.indexOf("(") + 1, q.indexOf(")"));
			Map<String, String> newSub = unify(q, subgoal, substi);

			if (newSub != null) 
			{
				newSub = compose(substi, newSub);
				List<String> LHS = new ArrayList<>();
				if (list.length != 1) {
					String lhs[] = list[0].split("\\^");

					for (int i = 0; i < lhs.length; i++) {
						lhs[i] = lhs[i].trim();
						lhs[i]=substitute(lhs[i], newSub);
						LHS.add(lhs[i]);
					}
				}
				
				if(checkLoops(LHS))
				{
					System.out.println("loop detected...!");
					continue;
				}
				
				if(islooprecursion(LHS,copy_subgoal))
				{
					System.out.println("loop detected.rec..!");
					continue;
				}
				 
				
				List<Map<String, String>> answers1;
				loopDetectionList.add(copy_subgoal);
				answers1 = (Backward_chaining(LHS, newSub));
				

				for (Map<String, String> theta : answers1) {
					answer.add(theta);
				}

			}
		} // for string

		String m = null;
		if(!loopDetectionList.isEmpty())
			 m=loopDetectionList.get(0);
		loopDetectionList= new ArrayList<>();
		loopDetectionList.add(m);
		//loopDetectionList.add(subgoal);
		List<Map<String, String>> finalAnswer = new ArrayList<>();
		for (Map<String, String> theta : answer) {
			List<Map<String, String>> answers1;
			List<String> copylistGoals=new ArrayList<>();
			copylistGoals.addAll(goals);
			answers1 = Backward_chaining(copylistGoals, theta);
			
			for (Map<String, String> theta1 : answers1)
				finalAnswer.add(theta1);
		}
		return finalAnswer;

	}

	private boolean compare_with_goals(String copy_subgoal) {
		List<String> mylist= new ArrayList<>();
		
		mylist.add(copy_subgoal);
		System.out.println("loop:"+loopDetectionList);
		System.out.println("copy_sub"+copy_subgoal);
		for(String s:loopDetectionList)
		{
			if(islooprecursion(mylist, s))
			{
				System.out.println("###returning true...!");
				return true;
			}
		}
		return false;
	}
	private boolean islooprecursion(List<String> LHS, String RHS) {
		int j=0;
		
		String substr2=RHS.substring(RHS.indexOf("(")+1,RHS.indexOf(")"));
		String args2[]=substr2.split(",");
		for(String s: LHS)
		{
			if(getPredicate(s).equals(getPredicate(RHS)))
			{
				String substr=s.substring(RHS.indexOf("(")+1,s.indexOf(")"));
				String args[]=substr.split(",");
				for( j=0;j<args.length;j++)
				{
			
					if(isVar(args[j] )&& isVar(args2[j]))
					{
						int k=0;
						while(args[j].charAt(k)==args2[j].charAt(k) && Character.isAlphabetic(args[j].charAt(k)))
						{
							k++;
						}
						if(k==0)
							break;
						else
							
						{
							int no1=Integer.parseInt(args[j].substring(k,args[j].length()));
							int no2=Integer.parseInt(args2[j].substring(k,args2[j].length()));
							if(no1!=no2)
							{
								continue;
							}
						}
					}
					else
					{
						System.out.println("++++++++++const found");
						if(args[j].equals(args2[j]))
						{
							continue;
						}
						else 
							break;
					}
				}
				if(j==args.length)
				{
					
					return true;
				}
			}
		}
		System.out.println("@@@@@@2returning false..!");
		return false;
	}
	private boolean checkLoops(List<String> list) {
		Iterator<String >iterator=list.iterator();
		if(iterator.hasNext())
		{
			String s=iterator.next();
			List<String> extra= new ArrayList<>();
			while(allVars(s))
			{
				iterator.remove();
				extra.add(s);
				if(iterator.hasNext())
					s=iterator.next();
				else
				{
					for(String str:extra)
					{
						list.add(str);
					}
					int flag=0;
					for( String str : list)
					{
						System.out.println("here");
						flag=0;
						List<String> rules=KB.get(getPredicate(str));
						if(rules.isEmpty())
							return true;
						/*else
						{
							for(String rule:rules)
							{
								if(isFact(rule))
								{
									flag=1;
									break;
								}
								else
								{
									String[] mylist=rule.split(" => ");
									List<String> LHS= new ArrayList<>();
									String[] lhs=mylist[0].split("\\^");
									for(int i=0;i<lhs.length;i++)
									{
										lhs[i]=lhs[i].trim();
										LHS.add(lhs[i]);
									}
									if(!checkLoops(LHS))
									{
										flag=1;
										break;
									}//if
								}//else
						
							}
							if(flag==0 )
								return true;
						}//else */
						
						}//else
					return false;
				}//iterator ha next
			}//while
			for(String str:extra)
			{
				list.add(str);
			}
		}//iterator not empty
		return false;
	}//fun
	
	private boolean isFact(String rule) {
		if(rule.contains("=>"))
			return false;
		return true;
	}
	
	private boolean allVars(String s) {
		
		String subst= s.substring(s.indexOf("(")+1,s.indexOf(")"));
		String[] args= subst.split(",");
		
		
		for(int j=0;j<args.length;j++)
		{
			if(!isVar(args[j]))
			{
				return false;
			}
			
		}
	return true;
	}
	private Map<String, String> compose(Map<String, String> substitution, Map<String, String> newSub) {

		Map<String, String> finalSub= new HashMap<>();
		
		for(Entry<String,String> entry:substitution.entrySet())
		{
			finalSub.put(entry.getKey(), entry.getValue());
		}
		
		for (Entry<String, String> entry : newSub.entrySet()) {
			if (!finalSub.containsKey(entry.getKey())) {
				finalSub.put(entry.getKey(), entry.getValue());
			}
		}

		return finalSub;
	}

	private Map<String, String> unify(String term1, String term2, Map<String, String> substi) {

		if (substi == null)
			return null;
		else if (term1.equals(term2))
			return substi;
		else if (isVar(term1)) {
			return unifyVar(term1, term2, substi);
		} else if (isVar(term2)) {
			return unifyVar(term2, term1, substi);
		}

		else if (isList(term1) && isList(term2)) {
			int end1 = term1.indexOf(",");
			String firstArgTerm1 = term1.substring(0, end1);

			int end2 = term2.indexOf(",");
			String firstArgTerm2 = term2.substring(0, end2);

			String restterm1 = term1.substring(end1 + 1, term1.length());
			String restterm2 = term2.substring(end2 + 1, term2.length());

			return unify(restterm1, restterm2, unify(firstArgTerm1, firstArgTerm2, substi));

		} else
			return null;
	}

	private boolean isList(String term1) {
		if (term1.contains(",")) {
			return true;
		}
		return false;
	}

	private boolean isVar(String term1) {

		if (!term1.contains(",") && Character.isLowerCase(term1.charAt(0))) {
			return true;
		}
		return false;
	}

	private Map<String, String> unifyVar(String term1, String term2, Map<String, String> substi) {
		
		Map<String, String> fsubstitution= new HashMap<>();
		if (substi.containsKey(term1)) {
			return unify(substi.get(term1), term2, substi);

		} else if (substi.containsKey(term2)) {
			return unify(term1, substi.get(term2), substi);
		} 
		else {
			for(Entry<String,String>entry:substi.entrySet())
			{
				fsubstitution.put(entry.getKey(), entry.getValue());
			}
			fsubstitution.put(term1, term2);
			return fsubstitution;
		}
	}

	/*
	 * private boolean occurs_check(String term1, String term2) {
	 * 
	 * return false; }
	 */

	public String getPredicate(String s) {
		String l[] = s.split("\\(");
		return l[0];
	}

	private String substitute(String goal, Map<String, String> substi) {

		//System.out.println(goal);
		String result = null;
		String list[] = goal.split("\\(");
		String predicate = list[0];
		System.out.println("predicate s:"+predicate);
		String args = list[1];
		args = args.substring(0, args.length() - 1);
		String arglist[] = args.split(",");
		/*for (int i = 0; i < arglist.length; i++)
			System.out.println(arglist[i]);
		*/String finalArgs = "";
		//System.out.println(substi);
		for (String a : arglist) {
			if (substi.containsKey(a)) {
				finalArgs = finalArgs + substi.get(a) + ",";
			} else
				finalArgs = finalArgs + a + ",";

		}
		finalArgs = finalArgs.substring(0, finalArgs.length() - 1);
		result = predicate + "(" + finalArgs + ")";
		return result;

	}

	private void print_KB() {
		for (Map.Entry<String, List<String>> entry : KB.entrySet()) {
			System.out.println("Key :" + entry.getKey() + " value: " + entry.getValue());
		}

	}

	private void add_sentence(String readLine) {
		String l1[] = readLine.split(" => ");
		String predicate;
		if (l1.length == 1) {
			String l2[] = readLine.split("\\(");
			predicate = l2[0];

		} else {
			String l2[] = l1[1].split("\\(");
			predicate = l2[0];
		}

		insert(predicate, readLine);

	}

	private void insert(String predicate, String readLine) {
		if (KB.containsKey(predicate)) {
			List<String> list = KB.get(predicate);
			list.add(readLine);
			KB.put(predicate, list);
		} else {
			List<String> list = new ArrayList<>();
			list.add(readLine);
			KB.put(predicate, list);
		}

	}
}