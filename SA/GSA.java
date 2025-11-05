package SA;
import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStreamReader;
import java.util.*;

public class GSA {

    static class NKA{
        HashSet<NKATransition> transitions;
        HashSet<State> states;
        HashSet<State> acceptedStates;
        State startingState;

        public NKA(HashSet<NKATransition> transitions, HashSet<State> states, HashSet<State> acceptedStates, State startingState){
            this.transitions = transitions;
            this.states = states;
            this.acceptedStates = acceptedStates;
            this.startingState = startingState;
        }

        public NKA() {
            transitions = new HashSet<>();
            states = new HashSet<>();
            acceptedStates = new HashSet<>();
            startingState = null;
        }
    }

    static class NKATransition{
        State start;
        State end;
        String transSymb;

        public NKATransition(State start, State end, String transSymb){
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
            return o instanceof NKATransition s && this.hashCode() == s.hashCode();
        }
        @Override
        public int hashCode(){
            return Objects.hash(start, end, transSymb);
        }
    }

    public static class DKA{
        HashSet<DKATransition> transitions;
        HashSet<Set<State>> states;
        HashSet<Set<State>> acceptedStates;
        Set<State> startingState;

        public DKA(){
            transitions = new HashSet<>();
            states = new HashSet<>();
            acceptedStates = new HashSet<>();
            startingState = new HashSet<>();
        }
    }

    static class DKATransition{
        Set<State> start;
        Set<State> end;
        String transSymb;
        public DKATransition(Set<State> start, Set<State> end, String transSymb){
            this.start = start;
            this.end = end;
            this.transSymb = transSymb;
        }

        @Override
        public String toString(){
            return start.toString() + " -> " + end.toString() + " -> " + transSymb;
        }
        @Override
        public int hashCode(){
            return Objects.hash(start, end, transSymb);
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

        public ArrayList<String> suffix(){
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
            return o instanceof State s && hashCode() == s.hashCode();
        }
        @Override
        public int hashCode(){
            return Objects.hash(item, pointer, T);
        }
    }

    static Map<Integer, State> stateCache = new HashMap<>();
    private static State getOrCreateState(Production prod, Set<String> T, int pointer) {
        int key = Objects.hash(prod, T, pointer);
        stateCache.computeIfAbsent(key, _ -> new State(prod, new HashSet<>(T), pointer));
        return stateCache.get(key);
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
            return o instanceof State s && hashCode() == s.hashCode();
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
                assert temp != null;
                temp.right.addAll(Arrays.asList(parts));
                temp.right.removeFirst();
            }
        }
    }

    static boolean[][] StartsWithTable;
    static Map<ArrayList<String>, HashSet<String>> startsWithCache = new HashMap<>();

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

        // Precompute Starts With
        startsWithCache.put(new ArrayList<>(), new HashSet<>());
        ArrayList<String> temp = new ArrayList<>();
        temp.add("$");
        startsWithCache.put(temp, new HashSet<>());

        for(Production prod : productions){
            if(prod.right.isEmpty() || prod.right.getFirst().equals("$")) continue;

            for(int i = 0; i < prod.right.size(); i++){
                ArrayList<String> key = new ArrayList<>();
                for(int j = i; j < prod.right.size(); j++)
                    key.add(prod.right.get(j));

                HashSet<String> value = new HashSet<>();
                for (String s : key) {
                    if (terminated.contains(s)) {
                        value.add(s);
                        break;
                    }
                    if (!empty.contains(s)) {
                        int idx = unterminated.indexOf(s);
                        for(int j = 0; j < terminated.size(); j++)
                            if(StartsWithTable[idx][j])
                                value.add(terminated.get(j));
                        break;
                    }
                    int idx = unterminated.indexOf(s);
                    for(int j = 0; j < terminated.size(); j++)
                        if(StartsWithTable[idx][j])
                            value.add(terminated.get(j));
                }
                startsWithCache.put(key, value);
            }
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



    private static NKA constructNKA(){
        HashSet<NKATransition> transitions = new HashSet<>();
        HashSet<State> currStates = new HashSet<>();
        Production temp = new Production("<S'>", new ArrayList<>());
        State startingState = getOrCreateState(temp, new HashSet<>(), 0);

        for(Production production : productions)
            if(production.left.equals(unterminated.getFirst())) {
                HashSet<String> T = new HashSet<>();
                T.add("END");
                State S;
                if(production.right.getFirst().equals("$"))
                    S = getOrCreateState(production, T, 1);
                else
                    S = getOrCreateState(production, T, 0);
                currStates.add(S);

                transitions.add(new NKATransition(startingState, S, "$"));
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
                State newState = getOrCreateState(curr.item, T, curr.pointer + 1);

                if(allStates.add(newState))
                    currStates2.add(newState);

                transitions.add(new NKATransition(curr, newState, curr.nextSymb()));

                if(terminated.contains(curr.nextSymb())) continue;

                for(Production production : productions){
                    if(production.left.equals(curr.nextSymb())) {
                        // Calculate FIRST(suffix + curr.T)
                        HashSet<String> newT = new HashSet<>();

                        // Get FIRST of the suffix
                        HashSet<String> firstOfSuffix = startsWithCache.get(curr.suffix());

                        if(firstOfSuffix == null || firstOfSuffix.isEmpty() || canBeEmpty(curr.suffix())) {
                            // If suffix can be empty, include curr.T
                            if(firstOfSuffix != null) {
                                newT.addAll(firstOfSuffix);
                            }
                            newT.addAll(curr.T);
                        } else {
                            // Otherwise just use FIRST(suffix)
                            newT.addAll(firstOfSuffix);
                        }

                        State newS;
                        if(production.right.getFirst().equals("$"))
                            newS = getOrCreateState(production, newT, 1);
                        else
                            newS = getOrCreateState(production, newT, 0);
                        if(allStates.add(newS))
                            currStates2.add(newS);
                        transitions.add(new NKATransition(curr, newS, "$"));
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
        allStates.add(startingState);

        return new NKA(transitions, allStates, acceptedStates, startingState);
    }

    private static boolean canBeEmpty(ArrayList<String> symbols) {
        if(symbols.isEmpty()) return true;
        for(String symbol : symbols) {
            if(!empty.contains(symbol)) {
                return false;
            }
        }
        return true;
    }

    private static DKA NKAtoDKA(NKA enka){
        NKA nka = new NKA();
        DKA dka = new DKA();

        // eNKA -> NKA
        // states remain the same, starting state also
        nka.states = new HashSet<>(enka.states);
        nka.startingState = enka.startingState;
        // acceptable states
        for (NKATransition t : enka.transitions) {
            if (t.start == enka.startingState && t.transSymb.equals("$")) {
                State temp = t.end;
                if (enka.acceptedStates.contains(temp)) {
                    nka.acceptedStates.add(t.start);
                    break;
                }
            }
        }
        nka.transitions = new HashSet<>(enka.transitions);

        // NKA -> DKA
        // all subsets of states
        List<State> stateList = new ArrayList<>(nka.states);
        int n = stateList.size();
        HashSet<Set<State>> setOfSubsets = new HashSet<>();

        int subsetNumber = 1 << n;
        for (int i = 0; i < subsetNumber; i++) {
            Set<State> subset = new HashSet<>();
            for (int j = 0; j < n; j++) {
                if ((i & (1 << j)) != 0) {
                    subset.add(stateList.get(j));
                }
            }
            setOfSubsets.add(subset);
        }

        dka.states = setOfSubsets;

        // acceptable states
        for (Set<State> subset : setOfSubsets) {
            for (State state : subset) {
                if (nka.acceptedStates.contains(state)){
                    dka.acceptedStates.add(subset);
                    break;
                }
            }
        }

        // starting state in a set
        dka.startingState = new HashSet<>();
        dka.startingState.add(nka.startingState);

        // transition functions
        // take all transition symbols from nka
        Set<String> alphabet = new HashSet<>();
        for (NKATransition t : nka.transitions) {
            if (!t.transSymb.equals("$")) { // exclude epsilon
                alphabet.add(t.transSymb);
            }
        }

        // generate all new transitions for dka
        for (Set<State> subset : setOfSubsets) {
            for (String symb : alphabet) {
                Set<State> newSubset = new HashSet<>();
                for (State s : subset) {
                    for (NKATransition t : nka.transitions) {
                        if (t.start.equals(s) && t.transSymb.equals(symb)) {
                            newSubset.add(t.end);
                        }
                    }
                }
                dka.transitions.add(new DKATransition(subset, newSubset, symb));
            }
        }

        return dka;
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
        System.out.println(nka.transitions.size());
        System.out.println(nka.states.size());
        DKA dka = NKAtoDKA(nka);

    }
}