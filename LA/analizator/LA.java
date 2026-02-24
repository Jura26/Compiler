package analizator;

import java.io.BufferedReader;
import java.io.FileReader;
import java.io.IOException;
import java.io.InputStreamReader;
import java.util.*;

public class LexicalAnalyzer {

    public static class Automaton {
        public String name;
        public int numStates;
        public ArrayList<Transition> transitions;
        public LinkedHashMap<Integer, ArrayList<String>> acceptable;

        public Automaton() {
            numStates = 1;
            transitions = new ArrayList<>();
            acceptable = new LinkedHashMap<>();
        }
    }

    public static class Transition {
        public int from;
        public int to;
        public char symbol;

        public Transition(int from, int to, char symbol) {
            this.from = from;
            this.to = to;
            this.symbol = symbol;
        }
    }

    static class State {
        String name;
        int id;

        public State(String name, int id) {
            this.name = name;
            this.id = id;
        }

        @Override
        public boolean equals(Object o) {
            if (this == o) return true;
            if (!(o instanceof State)) return false;
            State other = (State) o;
            return this.id == other.id && this.name.equals(other.name);
        }

        @Override
        public int hashCode() {
            return Objects.hash(name, id);
        }

        @Override
        public String toString() {
            return "(" + name + ", " + id + ")";
        }
    }

    static HashSet<State> acceptingStates = new HashSet<>();
    static LinkedHashMap<State, ArrayList<String>> stateToActions = new LinkedHashMap<>();
    static String input;
    static int lineNumber = 1;
    static ArrayList<Automaton> automatons = new ArrayList<>();
    static String currentStateName;

    public static void main(String[] args) throws IOException {
        loadFromFile("automats.txt");
        readInput();
        analyze();
    }

    public static void readInput() throws IOException {
        BufferedReader br = new BufferedReader(new InputStreamReader(System.in));
        StringBuilder sb = new StringBuilder();
        String line;
        while ((line = br.readLine()) != null) {
            sb.append(line);
            sb.append("\n");
        }
        input = sb.toString();
    }

    static int start = 0;
    static int last = 0;
    static int end = 0;
    static State expression = null;

    public static void analyze() {
        Set<State> R = new HashSet<>();
        R.add(new State(automatons.getFirst().name, 0));
        R = epsilonClosure(R);
        Set<State> startingStates = new HashSet<>(R);

        currentStateName = automatons.getFirst().name;

        while (end < input.length()) {
            char a = input.charAt(end);

            R = epsilonClosure(transition(R, a));
            end++;

            if (hasAcceptingState(R)) {
                expression = findExpression(R);
            }

            if (R.isEmpty()) {
                if (expression == null) {
                    printError(start);
                    start++;
                    end = start;

                    R.clear();
                    R.add(new State(currentStateName, 0));
                    R = epsilonClosure(R);

                } else {
                    R.clear();
                    State t = printToken();
                    if (t == null) {
                        R.add(new State(currentStateName, 0));
                        R = epsilonClosure(R);
                    } else {
                        R.add(t);
                        R = epsilonClosure(R);
                    }
                    expression = null;
                    end = last;
                }
            }
        }
    }

    public static Set<State> transition(Set<State> R, char a) {
        Set<State> result = new HashSet<>();

        for (State s : R)
            for (Automaton auto : automatons)
                if (auto.name.equals(s.name)) {
                    ArrayList<Transition> trans2 = auto.transitions;
                    for (Transition t : trans2)
                        if (t.from == s.id && t.symbol == a)
                            result.add(new State(s.name, t.to));
                }
        return result;
    }

    public static Set<State> epsilonClosure(Set<State> R) {
        Set<State> result = new HashSet<>(R);
        Stack<State> stack = new Stack<>();
        for (State s : R) {
            stack.push(s);
        }

        while (!stack.isEmpty()) {
            State temp = stack.pop();

            for (Automaton auto : automatons)
                if (auto.name.equals(temp.name)) {
                    ArrayList<Transition> trans2 = auto.transitions;
                    for (Transition t : trans2)
                        if (t.from == temp.id && t.symbol == '$') {
                            State e = new State(temp.name, t.to);
                            if (result.add(e))
                                stack.push(e);
                        }
                }
        }

        return result;
    }

    public static boolean hasAcceptingState(Set<State> R) {
        for (State s : R)
            if (acceptingStates.contains(s)) return true;
        return false;
    }

    public static State findExpression(Set<State> R) {
        HashSet<State> tempSet = new HashSet<>(R);
        tempSet.retainAll(acceptingStates);

        for (Map.Entry<State, ArrayList<String>> entry : stateToActions.entrySet())
            if (tempSet.contains(entry.getKey())) {
                last = end;
                return entry.getKey();
            }
        return null;
    }

    public static void printError(int position) {
        if (position < input.length()) {
            char symbol = input.charAt(position);
             System.err.println("Error: unrecognized symbol '" + symbol + "' at position " + position);
        } else {
             System.err.println("Lexical error at end of input.");
        }
    }

    public static State printToken() {
        State result = null;

        for (Map.Entry<State, ArrayList<String>> entry : stateToActions.entrySet()) {
            if (entry.getKey().equals(expression)) {
                // Handle VRATI_SE (RETURN)
                for (int i = 1; i < entry.getValue().size(); i++) {
                    if (entry.getValue().get(i).startsWith("VRATI_SE")) {
                        int temp = Integer.parseInt(entry.getValue().get(i).substring("VRATI_SE ".length()));
                        if (temp == 0) temp = 1;
                        last = last - temp;
                        end = end - temp;
                    }
                }

                String tokenText = input.substring(start, last);
                String tokenType = entry.getValue().getFirst();

                if (!tokenType.equals("-")) {
                    if (!tokenText.equals("''")) {
                        String displayText = tokenText
                                .replace("\\", "\\\\")
                                .replace("\n", "\\n")
                                .replace("\t", "\\t");
                        System.out.println(tokenType + " " + lineNumber + " " + displayText);
                    }
                }

                for (int i = 1; i < entry.getValue().size(); i++) {
                    if (entry.getValue().get(i).startsWith("UDJI_U_STANJE")) {
                        String temp = entry.getValue().get(i).substring("UDJI_U_STANJE ".length());
                        result = new State(temp, 0);
                        currentStateName = temp;
                    } else if (entry.getValue().get(i).equals("NOVI_REDAK")) {
                        lineNumber++;
                    }
                }

                start = last;
                end = last;

                break;
            }
        }
        return result;
    }

    public static void loadFromFile(String filename) {
        try (BufferedReader reader = new BufferedReader(new FileReader(filename))) {
            Automaton current = null;
            String line;

            while ((line = reader.readLine()) != null) {
                line = line.trim();
                if (line.isEmpty()) continue;

                if (line.startsWith("Automat:")) {
                    current = new Automaton();
                    current.name = line.substring("Automat:".length()).trim();
                    automatons.add(current);

                } else if (line.startsWith("Acceptable:")) {
                    while ((line = reader.readLine()) != null && !line.startsWith("Transitions:")) {
                        line = line.trim();
                        if (line.isEmpty()) continue;

                        if (!line.contains(":")) continue;

                        String[] parts = line.split(":", 2);
                        if (parts.length < 2) continue;

                        String left = parts[0].trim();
                        if (left.isEmpty()) continue;

                        int stateNum = Integer.parseInt(left);

                        String actionsStr = parts[1].trim();
                        State state = new State(current.name, stateNum);
                        acceptingStates.add(state);

                        ArrayList<String> actions = new ArrayList<>();
                        String[] split = actionsStr.split(",\\s*");
                        for (String s : split)
                            if (!s.isEmpty()) actions.add(s);
                        stateToActions.put(state, actions);
                    }
                } else if (line.matches("\\d+ --.+--> \\d+")) {
                    if (current != null) {
                        String[] parts = line.split(" ");
                        int from = Integer.parseInt(parts[0]);
                        String sym = parts[1].substring(2, parts[1].length() - 3);
                        char symbol;
                        if (sym.equals("$")) symbol = '$';
                        else if (sym.equals("\\n")) symbol = '\n';
                        else if (sym.equals("\\t")) symbol = '\t';
                        else if (sym.equals("\\_")) symbol = ' ';
                        else symbol = sym.charAt(0);
                        int to = Integer.parseInt(parts[2]);
                        current.transitions.add(new Transition(from, to, symbol));
                    }

                } else if (line.equals("-----")) {
                    current = null;
                }
            }

        } catch (IOException e) {
            e.printStackTrace();
        }
    }
}
