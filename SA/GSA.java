package SA;
import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStreamReader;
import java.util.*;

public class GSA {

    static class NKA{
        HashSet<Transition> transitions;
        HashSet<State> states;
        HashSet<State> acceptedStates;
        State startingState;

        public NKA(HashSet<Transition> transitions, HashSet<State> states, HashSet<State> acceptedStates, State startingState){
            this.transitions = transitions;
            this.states = states;
            this.acceptedStates = acceptedStates;
            this.startingState = startingState;
        }
    }

    static class State{
        Production item;
        int pointer;
        HashSet<String> T;
        boolean isStart;

        public State(Production item, HashSet<String> T, int pointer){
            this.item = item;
            this.T = T;
            this.pointer = pointer;
            this.isStart = false;
        }

        public String nextSymb(){
            return item.right.get(pointer);
        }

        public ArrayList<String> sufix(){
            ArrayList<String> res = new ArrayList<>();
            for(int i = pointer + 1; i < item.right.size(); i++)
                res.add(item.right.get(i));
            return res;
        }

        @Override
        public String toString(){
            return item.toString() + T + " " + pointer;
        }
        @Override
        public boolean equals(Object o){
            if(o instanceof State s)
                return item.equals(s.item) && T.equals(s.T) &&  pointer == s.pointer;
            return false;
        }
        @Override
        public int hashCode(){
            return Objects.hash(item, T, pointer);
        }
    }

    static class Transition{
        State start;
        State end;
        String transSymb;
        public Transition(State start, State end, String transSymb){
            this.start = start;
            this.end = end;
            this.transSymb = transSymb;
        }

        @Override
        public String toString(){
            return start.toString() + " -> " + end.toString() + " -> " + transSymb;
        }
        @Override
        public boolean equals(Object o){
            if(o instanceof Transition t)
                return start.equals(t.start) && end.equals(t.end) &&  transSymb.equals(t.transSymb);
            return false;
        }
        @Override
        public int hashCode(){
            return Objects.hash(start, end, transSymb);
        }
    }


    static class Production{
        // Left side of production
        String left;
        // Right side of production
        ArrayList<String> right;

        // Constructor
        Production(String left, ArrayList<String> right){
            this.left = left;
            this.right = right;
        }

        @Override
        public String toString(){
            return left + " -> " + right;
        }

        @Override
        public boolean equals(Object o){
            if(o instanceof Production t)
                return left.equals(t.left) && right.equals(t.right);
            return false;
        }
        @Override
        public int hashCode(){
            return Objects.hash(left, right);
        }
    }

    static ArrayList<String> unterminated = new ArrayList<>();
    static ArrayList<String> terminated = new ArrayList<>();
    static ArrayList<String> syncSymb = new ArrayList<>();
    static ArrayList<Production> productions = new ArrayList<>();

    // Function that parses input and stores it into above variables
    private static void ParseInput() throws IOException {
        BufferedReader br = new BufferedReader(new InputStreamReader(System.in));
        String line;
        Production temp = null;
        while ((line = br.readLine()) != null) {
            if (line.isEmpty()) continue;

            // Unterminated symbols
            if (line.startsWith("%V")){
                String[] parts = line.split(" ");
                unterminated.addAll(Arrays.asList(parts));
                unterminated.removeFirst();
                continue;
            }

            // Terminated symbols
            if (line.startsWith("%T")){
                String[] parts = line.split(" ");
                terminated.addAll(Arrays.asList(parts));
                terminated.removeFirst();
                continue;
            }

            // Synchronisation terminated symbols
            if (line.startsWith("%Syn")){
                String[] parts = line.split(" ");
                syncSymb.addAll(Arrays.asList(parts));
                syncSymb.removeFirst();
                continue;
            }

            // All productions
            if(!line.startsWith(" ")) {
                // Left side of production
                temp = new Production(line, new ArrayList<>());
                productions.add(temp);
            } else {
                // Right side of production
                if(!productions.getLast().right.isEmpty()){
                    // If it is not the first row it should construct next production instead of concatenating with |
                    temp = new Production(productions.getLast().left, new ArrayList<>());
                    productions.add(temp);
                }

                String[] parts = line.split(" ");
                temp.right.addAll(Arrays.asList(parts));
                temp.right.removeFirst();
            }
        }
    }

    static boolean[][] StartsWithTable;

    // Generate StartsWithTable and fills it
    private static void generateStartsWith(){
        boolean[][] DirectlyStartsWith = new boolean[unterminated.size()][unterminated.size() + terminated.size()];
        for (int i = 0; i < unterminated.size(); i++)
            for(int j = 0; j < unterminated.size() + terminated.size(); j++)
                DirectlyStartsWith[i][j] = false;

        // Fill DirectlyStartsWith
        for (Production prod : productions) {
            if(prod.right.getFirst().equals("$")) continue;

            int i = unterminated.indexOf(prod.left);

            int j;

            for(String right : prod.right){
                if(empty.contains(right)){
                    j =  unterminated.indexOf(right);
                    DirectlyStartsWith[i][j] = true;
                } else {
                    if(unterminated.contains(right))
                        j =  unterminated.indexOf(right);
                    else
                        j = terminated.indexOf(right) + unterminated.size();

                    DirectlyStartsWith[i][j] = true;
                    break;
                }

            }
        }

        boolean[][] StartsWith = Arrays.copyOf(DirectlyStartsWith, DirectlyStartsWith.length);

        // Fill (undirect) StartsWith
        for(int i = 0; i < unterminated.size(); i++){
            HashSet<Integer> used = new HashSet<>();
            Stack<Integer> stack = new Stack<>();
            for(int j = 0; j < unterminated.size(); j++)
                if(DirectlyStartsWith[i][j])
                    stack.push(j);
            while(!stack.isEmpty()){
                int top = stack.pop();
                if(used.contains(top)) continue;
                for(int j = unterminated.size(); j < terminated.size() + unterminated.size(); j++)
                    if(DirectlyStartsWith[top][j])
                        StartsWith[i][j] = true;
                used.add(top);
                for(int j = 0; j < unterminated.size(); j++)
                    if(DirectlyStartsWith[top][j]){
                        StartsWith[i][j] = true;
                        stack.push(j);
                    }
            }
        }

        // Keep only the right side of the table
        StartsWithTable = new boolean[unterminated.size()][terminated.size()];
        for(int i = 0; i < unterminated.size(); i++)
            for(int j = unterminated.size(); j < unterminated.size() + terminated.size(); j++){
                int idx = j - unterminated.size();
                StartsWithTable[i][idx] = StartsWith[i][j];
            }
    }

    // Decide which undetermined is "empty"
    static HashSet<String> empty;
    private static void calculateEmpty(){
        empty = new HashSet<>();
        for (Production production : productions)
            if (production.right.getFirst().equals("$"))
                empty.add(production.left);

        HashSet<String> empty2 = new HashSet<>();
        while(!empty.equals(empty2)){
            empty2.clear();
            empty2.addAll(empty);
            for (Production production : productions) {
                boolean add = true;
                for (String right : production.right)
                    if (!empty2.contains(right)) {
                        add = false;
                        break;
                    }
                if (add)
                    empty.add(production.left);
            }
        }
    }

    private static HashSet<String> startsWith(ArrayList<String> list){
        HashSet<String> res = new HashSet<>();
        if(list.isEmpty() || list.getFirst().equals("$")) return res;
        for (String s : list) {
            if (terminated.contains(s)) {
                res.add(s);
                break;
            }
            if (!empty.contains(s)) {
                res.addAll(startsWith(s));
                break;
            }
            res.addAll(startsWith(s));
        }
        return res;
    }
    private static HashSet<String> startsWith(String s){
        HashSet<String> res = new HashSet<>();

        int idx = unterminated.indexOf(s);

        for(int j = 0; j < terminated.size(); j++)
            if(StartsWithTable[idx][j])
                res.add(terminated.get(j));
        return res;
    }

    private static NKA constructNKA(){
        HashSet<Transition> transitions = new HashSet<>();
        HashSet<State> currStates = new HashSet<>();
        Production temp = new Production("<S'>", new ArrayList<>());
        State startingState = new State(temp, new HashSet<>(), 0);

        for(Production production : productions)
            if(production.left.equals(unterminated.getFirst())) {
                HashSet<String> T = new HashSet<>();
                T.add("END");
                State S = new State(production, T, 0);
                if(S.item.right.getFirst().equals("$"))
                    S.pointer++;
                currStates.add(S);

                transitions.add(new Transition(startingState, S, "$"));
            }

        HashSet<State> allStates = new HashSet<>(currStates);
        allStates.add(startingState);

        boolean finished;
        do {
            finished = true;
            HashSet<State> currStates2 = new HashSet<>();
            for (State curr : currStates) {
                if (curr.pointer == curr.item.right.size()) continue;
                finished = false;

                HashSet<String> T = new HashSet<>(curr.T);
                State newState = new State(curr.item, T, curr.pointer + 1);

                if(allStates.add(newState))
                    currStates2.add(newState);

                transitions.add(new Transition(curr, newState, curr.nextSymb()));

                if(terminated.contains(curr.nextSymb())) continue;

                for(Production production : productions){
                    if(production.left.equals(curr.nextSymb())) {
                        HashSet<String> newT = new HashSet<>(curr.T);
                        newT.addAll(startsWith(curr.sufix()));
                        State newS = new State(production, newT, 0);
                        if(newS.item.right.getFirst().equals("$"))
                            newS.pointer++;
                        if(allStates.add(newS))
                            currStates2.add(newS);
                        transitions.add(new Transition(curr, newS, "$"));
                    }
                }

            }
            currStates.clear();
            currStates.addAll(currStates2);
        } while(!finished);

        HashSet<State> acceptedStates = new HashSet<>();
        for(State state: allStates)
            if(state.pointer == state.item.right.size())
                acceptedStates.add(state);

        return new NKA(transitions, allStates, acceptedStates, startingState);
    }

    public static void main(String[] args) {
        try {
            ParseInput();
        }
        catch (IOException e) {
            e.printStackTrace();
        }
        calculateEmpty();
        generateStartsWith();
        NKA nka = constructNKA();
        for(Transition s: nka.transitions)
            System.out.println(s);
    }
}
