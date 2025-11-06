package SA;
import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStreamReader;
import java.util.*;

public class GSA {

    static class NFA{
        HashSet<NFATransition> transitions;
        HashSet<State> states;
        HashSet<State> acceptedStates;
        State startingState;

        public NFA(HashSet<NFATransition> transitions, HashSet<State> states, HashSet<State> acceptedStates, State startingState){
            this.transitions = transitions;
            this.states = states;
            this.acceptedStates = acceptedStates;
            this.startingState = startingState;
        }

        public NFA() {
            transitions = new HashSet<>();
            states = new HashSet<>();
            acceptedStates = new HashSet<>();
            startingState = null;
        }
    }

    static class NFATransition{
        State start;
        State end;
        String transSymb;

        public NFATransition(State start, State end, String transSymb){
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
            return o instanceof NFATransition s && this.hashCode() == s.hashCode();
        }
        @Override
        public int hashCode(){
            return Objects.hash(start, end, transSymb);
        }
    }

    public static class DFA{
        HashSet<DFATransition> transitions;
        HashSet<Set<State>> states;
        HashSet<Set<State>> acceptedStates;
        Set<State> startingState;

        public DFA(){
            transitions = new HashSet<>();
            states = new HashSet<>();
            acceptedStates = new HashSet<>();
            startingState = new HashSet<>();
        }
    }

    static class DFATransition{
        Set<State> start;
        Set<State> end;
        String transSymb;
        public DFATransition(Set<State> start, Set<State> end, String transSymb){
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

    private static NFA constructNFA(){
        HashSet<NFATransition> transitions = new HashSet<>();
        HashSet<State> currStates = new HashSet<>();
        ArrayList<String> RightProduction = new  ArrayList<>();
        RightProduction.add(unterminated.getFirst());
        Production temp = new Production("<%>", RightProduction);
        HashSet<String> startingT = new HashSet<>();
        startingT.add("#");
        State startingState = new State(temp, startingT, 0);

        currStates.add(startingState);
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

                transitions.add(new NFATransition(curr, newState, curr.nextSymb()));

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
                            newS = new State(production, newT, 1);
                        else
                            newS = new State(production, newT, 0);
                        if(allStates.add(newS))
                            currStates2.add(newS);
                        transitions.add(new NFATransition(curr, newS, "$"));
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

        return new NFA(transitions, allStates, acceptedStates, startingState);
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

    private static DFA NFAtoDFA(NFA nka) {
        DFA dka = new DFA();

        // starting state -> get epsilon closure
        Set<State> startSet = new HashSet<>();
        startSet.add(nka.startingState);
        startSet = epsilonClosure(startSet, nka);

        dka.startingState = startSet;

        Map<Set<State>, Set<State>> canonicalSets = new HashMap<>();
        HashSet<Set<State>> dkaStates = new HashSet<>();
        Queue<Set<State>> queue = new LinkedList<>();

        Set<State> canonicalStart = getCanonical(canonicalSets, startSet);
        dkaStates.add(canonicalStart);
        queue.add(canonicalStart);

        // get all transition symbols
        Set<String> alphabet = new HashSet<>();
        for (NFATransition t : nka.transitions) {
            if (!t.transSymb.equals("$")) alphabet.add(t.transSymb);
        }

        Map<State, Map<String, Set<State>>> outgoing = new HashMap<>();
        for (NFATransition t : nka.transitions) {
            if (!t.transSymb.equals("$")) {
                outgoing.computeIfAbsent(t.start, k -> new HashMap<>())
                        .computeIfAbsent(t.transSymb, k -> new HashSet<>())
                        .add(t.end);
            }
        }

        Map<Set<State>, Set<State>> epsilonCache = new HashMap<>();

        while (!queue.isEmpty()) {
            Set<State> current = queue.poll();

            for (String symb : alphabet) {
                Set<State> newSet = new HashSet<>();
                for (State s : current) {
                    newSet.addAll(outgoing.getOrDefault(s, Collections.emptyMap())
                            .getOrDefault(symb, Collections.emptySet()));
                }

                // memorirani epsilon closure
                newSet = epsilonCache.computeIfAbsent(newSet, k -> epsilonClosure(k, nka));

                if (newSet.isEmpty()) continue;

                Set<State> canonicalNew = canonicalSets.computeIfAbsent(newSet, k -> k);
                if (!dkaStates.contains(canonicalNew)) {
                    dkaStates.add(canonicalNew);
                    queue.add(canonicalNew);
                }

                dka.transitions.add(new DFATransition(canonicalSets.get(current), canonicalNew, symb));
            }
        }

        dka.states = dkaStates;
        for (Set<State> sSet : dkaStates) {
            for (State s : sSet) {
                if (nka.acceptedStates.contains(s)) {
                    dka.acceptedStates.add(sSet);
                    break;
                }
            }
        }

        return dka;
    }


    private static Set<State> epsilonClosure(Set<State> states, NFA nka) {
        Set<State> closure = new HashSet<>(states);
        Stack<State> stack = new Stack<>();
        stack.addAll(states);

        while (!stack.isEmpty()) {
            State s = stack.pop();
            for (NFATransition t : nka.transitions) {
                if (t.start.equals(s) && t.transSymb.equals("$") && !closure.contains(t.end)) {
                    closure.add(t.end);
                    stack.push(t.end);
                }
            }
        }
        return closure;
    }

    // helper function to get item from set if it already exists
    private static Set<State> getCanonical(Map<Set<State>, Set<State>> map, Set<State> subset) {
        for (Set<State> s : map.keySet()) {
            if (s.equals(subset)) return map.get(s);
        }
        map.put(subset, subset);
        return subset;
    }

    private static DFA minimizeDFA(DFA dka) {

        // find reachable states
        Set<Set<State>> reachableStates = new HashSet<>();
        reachableStates.add(dka.startingState);

        boolean added = true;
        while (added) {
            added = false;
            Set<Set<State>> temp = new HashSet<>(reachableStates);
            for (Set<State> stateSet : temp) {
                for (DFATransition t : dka.transitions) {
                    if (t.start.equals(stateSet) && !reachableStates.contains(t.end)) {
                        reachableStates.add(t.end);
                        added = true;
                    }
                }
            }
        }

        // keep only reachable states
        dka.states.retainAll(reachableStates);
        dka.acceptedStates.retainAll(reachableStates);
        dka.transitions.removeIf(t -> !reachableStates.contains(t.start) || !reachableStates.contains(t.end));

        // initial grouping of states
        Set<Set<State>> nonAccepted = new HashSet<>(dka.states);
        nonAccepted.removeAll(dka.acceptedStates);

        Set<Set<Set<State>>> groups = new HashSet<>();
        if (!dka.acceptedStates.isEmpty()) groups.add(new HashSet<>(dka.acceptedStates));
        if (!nonAccepted.isEmpty()) groups.add(nonAccepted);

        // minimization through iterations
        // get all transition symbols
        Set<String> alphabet = new HashSet<>();
        for (DFATransition t : dka.transitions) {
            if (!t.transSymb.equals("$")) alphabet.add(t.transSymb);
        }
        boolean changed = true;

        while (changed) {
            changed = false;
            Set<Set<Set<State>>> newGroups = new HashSet<>(groups);

            for (Set<Set<State>> group : groups) {
                Map<Map<String, Set<Set<State>>>, Set<Set<State>>> partitionMap = new HashMap<>();

                for (Set<State> state : group) {
                    Map<String, Set<Set<State>>> signature = new HashMap<>();
                    for (String symbol : alphabet) {
                        Set<Set<State>> targetGroup = null;
                        for (DFATransition t : dka.transitions) {
                            if (t.start.equals(state) && t.transSymb.equals(symbol)) {
                                for (Set<Set<State>> g : groups) {
                                    if (g.contains(t.end)) {
                                        targetGroup = g;
                                        break;
                                    }
                                }
                            }
                        }
                        signature.put(symbol, targetGroup);
                    }
                    partitionMap.computeIfAbsent(signature, k -> new HashSet<>()).add(state);
                }

                if (partitionMap.size() > 1) {
                    newGroups.remove(group);
                    newGroups.addAll(partitionMap.values());
                    changed = true;
                    break;
                }
            }

            groups = newGroups;
        }

        // pick a state to represent every equivalent pair
        Set<Set<State>> minStates = new HashSet<>();
        for (Set<Set<State>> group : groups) {
            if (!group.isEmpty()) {
                List<Set<State>> sortedGroup = new ArrayList<>(group);
                sortedGroup.sort(Comparator.comparing(Set::toString));
                Set<State> representative = sortedGroup.get(0);
                minStates.add(representative);

                for (DFATransition t : dka.transitions) {
                    if (group.contains(t.start)) t.start = representative;
                    if (group.contains(t.end)) t.end = representative;
                }

                if (group.contains(dka.startingState)) dka.startingState = representative;
            }
        }

//        // keep only minimal states
//        dka.states.retainAll(minStates);
//        dka.acceptedStates.retainAll(minStates);
//        dka.transitions.removeIf(t -> !minStates.contains(t.start) || !minStates.contains(t.end));

        return dka;
    }

    private static void createTables(DFA dfa){

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
        NFA nfa = constructNFA();
        DFA dfa = NFAtoDFA(nfa);
        DFA dfaMin = minimizeDFA(dfa);

    }
}