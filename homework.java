import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.File;
import java.io.FileReader;
import java.io.FileWriter;
import java.io.IOException;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;
import java.util.Stack;
import java.util.TreeMap;

class Clause{

	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + ((clause == null) ? 0 : clause.hashCode());
		return result;
	}
	@Override
	public boolean equals(Object obj) {
		if (this == obj)
			return true;
		if (obj == null)
			return false;
		if (getClass() != obj.getClass())
			return false;
		Clause other = (Clause) obj;
		if (clause == null) {
			if (other.clause != null)
				return false;
		} else if (!clause.equals(other.clause))
			return false;
		return true;
	}
	Set<Predicate> clause; 
	Clause(Set<Predicate> clause){
		this.clause = clause;
	}	
	
	void display(){
		for(Predicate p : clause){
			p.display();
			System.out.print(" | ");
		}
		System.out.println();
	}
	
	
}

class Predicate{
	
	String name;
	boolean isNegative;
	String args[];
	
	public Predicate(String name, boolean isNegative, String[] args) {
		super();
		this.name = name;
		this.isNegative = isNegative;
		this.args = args;
	}
	
	public void display(){
		System.out.print((isNegative?" ~":" ")+name+"(");
		for(String arg : args ){
			System.out.print(arg+", ");
		}
		System.out.print(") ");
	}
	
	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		
		for(int i=0;i<args.length;i++){
			if(args[i]==null){
				result = prime * result;
			} else {
				char firstLetterOne  = args[i].charAt(0);
				boolean isVariableOne = ('a' <= firstLetterOne && firstLetterOne <='z' )? true: false;
				if(!isVariableOne){
					result = prime * result+ args[i].hashCode();
				}
			}
		}
		result = prime * result + (isNegative ? 1231 : 1237);
		result = prime * result + ((name == null) ? 0 : name.hashCode());
		return result;
	}

	@Override
	public boolean equals(Object obj) {
		if (this == obj)
			return true;
		if (obj == null)
			return false;
		if (getClass() != obj.getClass())
			return false;
		Predicate other = (Predicate) obj;
		
		if (isNegative != other.isNegative)
			return false;
		if (name == null) {
			if (other.name != null)
				return false;
		} else if (!name.equals(other.name))
			return false;
		
		if(args==null){
			if(other.args!=null){
				return false;
			}
		}
		
		if(args.length!=other.args.length){
			return false;
		}
		
		for(int i = 0;i < args.length; i++){
			char firstLetterOne  = args[i].charAt(0);
			char firstLetterTwo = other.args[i].charAt(0);
			
			boolean isVariableOne = ('a' <= firstLetterOne && firstLetterOne <='z' )? true: false;
			boolean isVariableTwo = ('a' <= firstLetterTwo && firstLetterTwo <='z' )? true: false;
			
			if(!isVariableOne && !isVariableTwo && !args[i].equals(other.args[i])){
				return false;
			}
			
			if( (isVariableOne && !isVariableTwo) || (!isVariableOne && isVariableTwo) ){
				return false;
			}
		}
		
		return true;
	}
	
}

public class homework {
		
	static long cntVariables=0;
	static HashMap<String,ArrayList<String>> predicateMapPositive = new HashMap<String, ArrayList<String>>();
	static HashMap<String,ArrayList<String>> predicateMapNegative =  new HashMap<String, ArrayList<String>>();
	static ArrayList<ArrayList<Predicate>> sentences = new ArrayList<ArrayList<Predicate>>();
	static Set<Clause> sentenceSet = new HashSet<Clause>();
	
	static void display(ArrayList<Predicate> sentence){
		for(Predicate p : sentence){
			p.display();
			System.out.print(" V ");
		}
		System.out.println();
	}
	
	static boolean isVariable(String s){
		if(s==null || s.length() ==0){
			return false;
		}
		return (s.charAt(0) >= 'a' && s.charAt(0) <='z');   
	}
	
	static ArrayList<Predicate> resolve(ArrayList<Predicate> s1, ArrayList<Predicate> s2, HashMap<String,String>theta, int pIndexOne ,int pIndexTwo){
		
		ArrayList<Predicate> substituted1 = new ArrayList<Predicate>();
		ArrayList<Predicate> substituted2 = new ArrayList<Predicate>();
		ArrayList<Predicate> resolved = new ArrayList<Predicate>();
		
		for(int i=0;i<s1.size();i++){
			if(i!=pIndexOne){
				substituted1.add(substitutePredicate(s1.get(i),theta));
			}
		}
		
		for(int i=0;i<s2.size();i++){
			if(i!=pIndexTwo){
				substituted2.add(substitutePredicate(s2.get(i),theta));
			}
		}
		
		
		HashSet <Predicate> set1 = new HashSet<Predicate>(substituted1);
		HashSet <Predicate> set2 = new HashSet<Predicate>(substituted2);
		for(int i=0;i<substituted1.size();i++){
			Predicate p1 = substituted1.get(i);
			Predicate p1Negated = new Predicate(p1.name,!p1.isNegative,p1.args.clone());
			if(set2.contains(p1Negated)){
				// remove it from here
				substituted1.remove(i);
			}
		}
		
		for(int i=0;i<substituted2.size();i++){
			Predicate p1 = substituted2.get(i);
			Predicate p1Negated = new Predicate(p1.name,!p1.isNegative,p1.args.clone());
			if(set1.contains(p1Negated)){
				// remove it from here
				substituted2.remove(i);
			}
		}
		
		
		resolved.addAll(substituted1);
		resolved.addAll(substituted2);
		return resolved;
		
	}
	
	static boolean unify(Predicate a , Predicate b , HashMap<String,String> theta){
		
		if(!a.name.equals(b.name)){
			return false;
		}
		return unifyVarList(a.args, b.args, theta);
	}
	
	static boolean unifyVarList (String [] l1, String [] l2,HashMap<String,String> theta){
		for(int i=0;i<l1.length;i++){
			if(!unifyVar(l1[i],l2[i],theta)){
				return false;
			}
		}
		return true;
	}
	
	public static HashMap<String, ArrayList<String>>copy(HashMap<String, ArrayList<String>> original)
	{
		HashMap<String, ArrayList<String>> copy = new HashMap<String, ArrayList<String>>();
		    for (Map.Entry<String, ArrayList<String>> entry : original.entrySet())
		    {
		        copy.put(entry.getKey(),
		           new ArrayList<String>(entry.getValue()));
		    }
		    return copy;
	}
	
	static boolean unifyVar(String var1 , String var2 , HashMap<String,String> theta){
		
		if(var1.equals(var2)){
			return true;
		}
		
		if(!isVariable(var1) && !isVariable(var2)){
			return false;
		}
		
		if(!isVariable(var1)){
			return unifyVar(var2,var1,theta);
		}
		
		if(theta.containsKey(var1)){
			return unifyVar(theta.get(var1),var2,theta);
		} else if(theta.containsKey(var2)) {
			return unifyVar(var1,theta.get(var2),theta);
		} else {
			theta.put(var1, var2);
			return true;
		}
		
	}
	
	
	static int addToSupport(ArrayList<Predicate> sentence, ArrayList<ArrayList<Predicate>> sos , 
			HashMap<String,ArrayList<String>> predicateMapPositiveCloned, 
			HashMap<String,ArrayList<String>> predicateMapNegativeCloned, 
			HashMap<Integer,TreeMap<Integer,ArrayList<String>>> resolveWith, HashSet<Clause> sosSet){
		
		int index=-1;
		if(sos!=null && sentence!=null && sentence.size() > 0){
			
		standardizeVariable(sentence);
		Set<Predicate> factoredSentence = new HashSet<Predicate>(sentence);
		Clause c = new Clause(factoredSentence);
		sosSet.add(c);
		sentence = new ArrayList<Predicate>(factoredSentence);
		
		sos.add(sentence);
		
		index = sos.size()-1;
		index = index+sentences.size();
		
		for(int j = 0 ;j<sentence.size(); j++){
			Predicate p = sentence.get(j);
			
				if(p.isNegative){
					
					if(predicateMapPositiveCloned.containsKey(p.name)){
						ArrayList<String> resolveWithStrings = predicateMapPositiveCloned.get(p.name);
						for(String rw : resolveWithStrings){
							int indexOf = rw.indexOf("_");
							int resolveWithSentenceIndex = Integer.parseInt(rw.substring(0, indexOf));
							int resolveWithpredicateIndex = Integer.parseInt(rw.substring(indexOf+1, rw.length()));
							
							int num_literals = 0;
							
							if(resolveWithSentenceIndex >= sentences.size()){
								int in = resolveWithSentenceIndex-sentences.size();
								num_literals = (sos.get(in)).size();
							} else {
								num_literals = (sentences.get(resolveWithSentenceIndex)).size();
							}
							
							addToResolutionMap(resolveWith, index, num_literals, resolveWithSentenceIndex, resolveWithpredicateIndex, j);
						}
						
					}
					
				} else {
					
					if(predicateMapNegativeCloned.containsKey(p.name)){
						
						ArrayList<String> resolveWithStrings = predicateMapNegativeCloned.get(p.name);
						for(String rw : resolveWithStrings){
							
							int indexOf = rw.indexOf("_");
							int resolveWithSentenceIndex = Integer.parseInt(rw.substring(0, indexOf));
							int resolveWithpredicateIndex = Integer.parseInt(rw.substring(indexOf+1, rw.length()));
							int num_literals = 0;

							if(resolveWithSentenceIndex >= sentences.size()){
								int in = resolveWithSentenceIndex-sentences.size();
								num_literals = (sos.get(in)).size();
							} else {
								num_literals = (sentences.get(resolveWithSentenceIndex)).size();
							}
							
							addToResolutionMap(resolveWith, index, num_literals, resolveWithSentenceIndex, resolveWithpredicateIndex, j);
						}
						
					}
					
				}
		}
		
		for(int j = 0 ;j<sentence.size(); j++){
			Predicate p = sentence.get(j);
			
				if(p.isNegative){
					addToPredicateMap(predicateMapNegativeCloned,p.name,index,j);
				} else {
					addToPredicateMap(predicateMapPositiveCloned,p.name,index,j);
				}
		}
		}
		
		return index;
		
	}
	
	
	static Predicate substitutePredicate(Predicate p1, HashMap<String,String> map){
		Predicate p2 = new Predicate(p1.name,p1.isNegative,p1.args.clone());
		String [] args = p2.args;
		for(int i =0;i<args.length;i++){
			if(map.containsKey(args[i])){
				args[i]= map.get(args[i]);
			}
		}
		return p2;
		
	}
	
	static void addToPredicateMap(HashMap<String,ArrayList<String>> map, String pName, int sentenceIndex, int predicateIndex){
		ArrayList<String> presentInSentences = new ArrayList<String>();
		if(map!=null){
				if(map.containsKey(pName)){
					presentInSentences = map.get(pName);
				} else {
					presentInSentences = new ArrayList<String>();
				}
				presentInSentences.add(sentenceIndex+"_"+predicateIndex);
				map.put(pName, presentInSentences);
		}
	}
	
	static void displayPredicateMap(HashMap<String,ArrayList<String>> map){
		
		if(map!=null){
				for(String p : map.keySet()){
					System.out.println(p+"->");
					for(String mapped : map.get(p)){
						System.out.print(mapped+"  ");
					}
					
					System.out.println();
				}
		}
	}
	
	static void displayResolutionMap(HashMap<Integer,TreeMap<Integer,ArrayList<String>>> map, ArrayList<ArrayList<Predicate>> sos){
		
		if(map!=null){
				for(Integer sentenceIndex : map.keySet()){
					System.out.println(sentenceIndex +"->");
					TreeMap<Integer,ArrayList<String>> tm = map.get(sentenceIndex);
					for(Integer num_literals : tm.keySet()){
						System.out.println(num_literals +"->");
						
						ArrayList<String> list = tm.get(num_literals);
						for(String rw : list){
							
							System.out.println("can be resolved with "+rw);
							int indexOf = rw.indexOf("_");
							int resolveWithSentenceIndex = Integer.parseInt(rw.substring(0, indexOf));
							String remaining = rw.substring(indexOf+1);
							indexOf = remaining.indexOf("_");
							int resolveWithpredicateIndex = Integer.parseInt(remaining.substring(0,indexOf));
							int predicateIndex =  Integer.parseInt(remaining.substring(indexOf+1));
							
							
							ArrayList<Predicate> sente = null;
							
							if(resolveWithSentenceIndex >= sentences.size()){
								resolveWithSentenceIndex = resolveWithSentenceIndex-sentences.size();
								sente = sos.get(resolveWithSentenceIndex);
							} else {
								sente = sentences.get(resolveWithSentenceIndex);
							}
						
							System.out.println("the sentence ");
							display(sos.get(sentenceIndex-sentences.size()));
							
							sos.get(sentenceIndex-sentences.size()).get(predicateIndex).display();
							
							System.out.println("gets resolved with");
						
							
							display(sente);
							
							sente.get(resolveWithpredicateIndex).display();
							
							
						}
					}
					
					System.out.println("----------------------------------------------------------------------");
				}
		}
	}
	
	
	static ArrayList<Predicate> getSentenceFromSentenceIndex(ArrayList<ArrayList<Predicate>> kb , ArrayList<ArrayList<Predicate>> sos, int sIndex){
		ArrayList<Predicate> sentence=null;
		if(sIndex<kb.size()){
			sentence = kb.get(sIndex);
		} else {
			sIndex = sIndex-kb.size();
			if(sIndex < sos.size()){
				sentence = sos.get(sIndex);
			}
		}
		
		return sentence;
	}
	
	static void addToResolutionMap(HashMap<Integer,TreeMap<Integer,ArrayList<String>>> map, Integer sentenceIndex ,
			Integer num_literals, int resolveWithSentenceIndex, int resolveWithpredicateIndex,int predicateIndex){
		ArrayList<String> resolveWithSentences ;
		TreeMap<Integer, ArrayList<String>> tm;
		if(map!=null){
				if(map.containsKey(sentenceIndex)){
					tm = map.get(sentenceIndex);
				} else {
					tm = new TreeMap<Integer, ArrayList<String>>();
				}
				
				if(tm.containsKey(num_literals)){
					resolveWithSentences = tm.get(num_literals);
				} else {
					resolveWithSentences = new ArrayList<String>();
				}
			
				resolveWithSentences.add(resolveWithSentenceIndex+"_"+resolveWithpredicateIndex+"_"+predicateIndex);
				tm.put(num_literals, resolveWithSentences);
				map.put(sentenceIndex, tm);
		}
	}
	
	static void addSentenceToKB(ArrayList<Predicate> sentence){
		
		if(sentence!=null && sentence.size() > 0){
			
		Set<Predicate> factoredSentence = new HashSet<Predicate>(sentence);
		Clause c = new Clause(factoredSentence);
		sentenceSet.add(c);
		sentence = new ArrayList<Predicate>(factoredSentence);
			
		sentences.add(sentence);
		int index = sentences.size()-1;
		
		for(int j = 0 ;j<sentence.size(); j++){
			Predicate p = sentence.get(j);
				if(p.isNegative){
					addToPredicateMap(predicateMapNegative,p.name,index,j);
				} else {
					addToPredicateMap(predicateMapPositive,p.name,index,j);
				}
		}
		}
	}
	
	static void standardizeVariable(ArrayList<Predicate> sentence){
		
		HashMap<String,Long> map= new HashMap<String,Long>();
		
		for(Predicate p : sentence){
			for(int j=0; j<p.args.length;j++){
				String [] args = p.args;
				char firstLetter = args[j].charAt(0);
				if(firstLetter >= 'a' && firstLetter <='z' ){
					if(map.containsKey(args[j])){
						args[j] = "x"+map.get(args[j]);
					} else {
						cntVariables++;
						map.put(args[j], cntVariables);
						args[j] = "x"+cntVariables;
					}
				}
				
			}
		}
	
	}
	
	
	static Predicate parsePredicate(String line, long[] mappedVariables){
		
		if(line==null)
			return null;
		
		line = line.trim();
		boolean isNegative = line.charAt(0)=='~'?true:false;
		int indexOfLeftBracket = line.indexOf('(');
		int beginIndex = isNegative? 1: 0;
		String predicateName = line.substring(beginIndex, indexOfLeftBracket);
		predicateName= predicateName.trim();
		int indexOfRightBracket = line.indexOf(')');
		String argumentString = line.substring(indexOfLeftBracket+1,indexOfRightBracket);
		
		String [] argsList = argumentString.split(",");
		for(int j =0;j <argsList.length;j++){
			argsList[j] = argsList[j].trim();
			char firstLetter = argsList[j].charAt(0);
			if(firstLetter >= 'a' && firstLetter <='z' ){
				if(mappedVariables[firstLetter-'a'] > 0){
					argsList[j]= "x"+mappedVariables[firstLetter-'a'];
				}else{
					cntVariables++;
					mappedVariables[firstLetter-'a']=cntVariables;
					argsList[j]="x"+cntVariables;
				}
			}
		}
		
		Predicate p= new Predicate(predicateName, isNegative, argsList);
		return p;
	}
	
	static String removeResolutionChoice(int sIndex, HashMap<Integer,TreeMap<Integer,ArrayList<String>>> resolutionMap){
		
		if(resolutionMap!=null && resolutionMap.containsKey(sIndex)){
			
			TreeMap<Integer,ArrayList<String>> tm = resolutionMap.get(sIndex);
			int key = tm.firstKey();
			ArrayList<String> list = tm.get(key);
			
			String returnValue = list.remove(0);
			
			if(list.isEmpty()){
				tm.remove(key);
				
				if(tm.isEmpty()){
					resolutionMap.remove(sIndex);
				}
			}
			
			return returnValue;
		}
		return null;
	}
	public static void main(String args[]){
	
		File dir = new File(".");
		File fin = null;
		int n_q;
		int n_s;
		ArrayList<Predicate> queries = new ArrayList<Predicate>();
		Boolean[] result =null;
		
		 
		long [] mappedVariables = new long[26];
		
		
		try {
			fin = new File("input.txt");
			if(fin!=null){
				
				BufferedReader br;
				br = new BufferedReader(new FileReader(fin));
				String line = null;
				
				n_q = Integer.parseInt(br.readLine().trim());
				result = new Boolean [n_q];
				int i = 0;
				
				while (i<n_q &&  (line = br.readLine()) != null) {
					Predicate p= parsePredicate(line,mappedVariables);
					queries.add(p);
						i++;
				}
				
				n_s = Integer.parseInt(br.readLine().trim()); 
				i=0;
				
				while (i<n_s &&  (line = br.readLine()) != null) {
					
					ArrayList<Predicate> sentence = new ArrayList<Predicate>();
					mappedVariables = new long[26];
					line = line.trim();
					String [] predicates = line.split("\\|");
					for(String ps : predicates){
						Predicate p= parsePredicate(ps,mappedVariables);
						sentence.add(p);
					}
					
					if(!sentence.isEmpty()){
						addSentenceToKB(sentence);
					}
					i++;
				}
				br.close();
			} 
		}catch (IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		} 
		
	
		for(int qIndex = 0;qIndex < queries.size() ; qIndex++){
			
			Predicate query = queries.get(qIndex);
			HashMap<String,ArrayList<String>> predicateMapPositiveCloned  =  copy(predicateMapPositive);
			HashMap<String,ArrayList<String>> predicateMapNegativeCloned  =  copy(predicateMapNegative);
			
//			displayPredicateMap(predicateMapNegativeCloned);
			
//			System.out.println("initially size of maps "+predicateMapPositiveCloned.size()+" "+predicateMapNegativeCloned.size());
			HashMap<Integer,TreeMap<Integer,ArrayList<String>>> resolveWith = new HashMap<Integer,TreeMap<Integer,ArrayList<String>>>();
			HashSet<Clause> sosSet = new HashSet<Clause>();
			
			ArrayList<ArrayList<Predicate>> sos = new ArrayList<ArrayList<Predicate>>();
			Predicate negatedQuery = new Predicate(new String(query.name),!query.isNegative,query.args.clone());
			ArrayList<Predicate> negatedSentence = new ArrayList<Predicate>();
			negatedSentence.add(negatedQuery);
			standardizeVariable(negatedSentence);
			int index = addToSupport(negatedSentence, sos, predicateMapPositiveCloned, predicateMapNegativeCloned, resolveWith,sosSet);
			
			Stack<Integer> stack = new Stack<Integer>();
			stack.push(index);
			
			boolean isProved = false;
			int i =0;
			
			while(!stack.isEmpty() ){
				// try to prove a contradiction and return true
				int nextSentence = stack.pop();
				String resolutionChoice = removeResolutionChoice(nextSentence, resolveWith);
				if(resolutionChoice!=null){
					
					int indexOf = resolutionChoice.indexOf("_");
					int resolveWithSentenceIndex = Integer.parseInt(resolutionChoice.substring(0, indexOf));
					String remaining = resolutionChoice.substring(indexOf+1);
					indexOf = remaining.indexOf("_");
					int resolveWithpredicateIndex = Integer.parseInt(remaining.substring(0,indexOf));
					int predicateIndex =  Integer.parseInt(remaining.substring(indexOf+1));
					
					ArrayList<Predicate> a = getSentenceFromSentenceIndex(sentences, sos, nextSentence);
					ArrayList<Predicate> b = getSentenceFromSentenceIndex(sentences, sos, resolveWithSentenceIndex);
					
//					System.out.println("trying to resolve ");
					//display(a);
//					System.out.println("against this");
//					display(b);
					
					HashSet<Predicate> aSet = new HashSet<Predicate>(a);
					HashSet<Predicate> bSet = new HashSet<Predicate>(b);
					
					
					int indexAdded = -1;
					
					if(a!=null && b!=null){
						HashMap<String,String> theta = new HashMap<String,String>();
						boolean unified = unify(a.get(predicateIndex),b.get(resolveWithpredicateIndex),theta);
						
						
						if(unified){
							ArrayList<Predicate> resolved = resolve(a,b, theta, predicateIndex ,resolveWithpredicateIndex);
////							
//							System.out.println("trying to resolve ");
//							display(a);
//							System.out.println("against this");
//							display(b);
//							System.out.println("got resolved to ");
//							display(resolved);
							
							if(resolved.size()>0){
								 
								 Clause resolvedClause = new Clause(new HashSet<Predicate>(resolved));
								 
								// System.out.println("does resolved clause contains aSet "+(resolvedClause.clause).containsAll(aSet));
								// System.out.println("does resolved clause contains bSet "+(resolvedClause.clause).containsAll(bSet));
								 
								if(!sentenceSet.contains(resolvedClause) && !sosSet.contains(resolvedClause) && !(resolvedClause.clause).containsAll(aSet) && !(resolvedClause.clause).containsAll(bSet)){
									// if the sentence is not already present, then only add this to sos. 
									 indexAdded = addToSupport(resolved, sos, predicateMapPositiveCloned, predicateMapNegativeCloned, resolveWith,sosSet);
								}
								
							} else {
								//System.out.println("the query is true");
								result[qIndex] = true;
								//query.display();;
								isProved = true;
								break;
							}
						}
					}
					
					if(resolveWith.containsKey(nextSentence)){
						stack.push(nextSentence);
					}
					if(indexAdded > 0 ){
						stack.push(indexAdded);
					}
					i++;
				}
			}
			
			if(stack.isEmpty() && !isProved){
				//System.out.println("the query is false");
				result[qIndex] = false;
				//query.display();;
			}
			
					
			}
		
		if( result!=null){
			
			BufferedWriter bw = null;
			FileWriter fw = null;

			try {

				fw = new FileWriter("output.txt");
				bw = new BufferedWriter(fw);
				for(int i =0;i < result.length;i++){
							bw.write(result[i].toString().toUpperCase());
							bw.newLine();
				}
			
				if (bw != null)
					bw.close();

				if (fw != null)
					fw.close();

			} catch (IOException e) {
				e.printStackTrace();
			} 		
		}
		
	}


}