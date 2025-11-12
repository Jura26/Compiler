package LA;
import java.io.*;
import java.util.*;

public class GLA {

    static class Rule {
        String name;
        String regex;
        ArrayList<String> actions = new ArrayList<>();

        @Override
        public String toString() {
            return "<" + this.name + "> " + this.regex + " " + this.actions;
        }
    }

    public static class Automat {
        public String name;
        public int numStates;
        public ArrayList<Transition> transitions;
        public LinkedHashMap<Integer, ArrayList<String>> acceptable;


        public Automat() {
            numStates = 1;
            transitions = new ArrayList<>();
            acceptable = new LinkedHashMap<>();
        }

    }

    public static class Transition{
        public int from;
        public int to;
        public char symbol;

        public Transition(int from, int to, char symbol) {
            this.from = from;
            this.to = to;
            this.symbol = symbol;
        }
    }

    public static class StatePair{
        int left;
        int right;
        public StatePair(int first, int second) {
            this.left = first;
            this.right = second;
        }
    }

    private int newState(Automat a) {
        return a.numStates++;
    }

    private boolean isOperator(String exp, int i) {
        int c = 0;
        while(i - 1 >= 0 && exp.charAt(i - 1) == '\\') {
            c++;
            i--;
        }
        return c % 2 == 0;
    }
    private static boolean isOperator2(String exp, int i) {
        int c = 0;
        while(i - 1 >= 0 && exp.charAt(i - 1) == '\\') {
            c++;
            i--;
        }
        return c % 2 == 1;
    }

    private int findMatchingParen(String regex, int start) {
        int depth = 0;
        for (int i = start; i < regex.length(); i++) {
            if (regex.charAt(i) == '(') depth++;
            else if (regex.charAt(i) == ')') {
                depth--;
                if (depth == 0) return i;
            }
        }
        return regex.length() - 1;
    }

    private static boolean containsBracket(String regex){
        for (int i = 0; i < regex.length(); i++)
            if (regex.charAt(i) == '{' && !isOperator2(regex, i))
                return true;
        return false;
    }

    private static int findFirstOpenBracket(String regex){
        for (int i = 0; i < regex.length(); i++)
            if (regex.charAt(i) == '{' && !isOperator2(regex, i))
                return i;
        return -1;
    }

    private static int findFirstClosedBracket(String regex){
        for (int i = 0; i < regex.length(); i++)
            if (regex.charAt(i) == '}' && !isOperator2(regex, i))
                return i;
        return -1;
    }

    public  StatePair exchange(String regex, Automat auto){
        ArrayList<String> poss = new ArrayList<>();
        int numBrackets = 0;

        int start = 0;
        for(int i = 0; i < regex.length(); i++) {
            if(regex.charAt(i) == '(' && isOperator(regex, i))
                numBrackets++;
            else if(regex.charAt(i) == ')' && isOperator(regex, i))
                numBrackets--;
            else if(numBrackets == 0 && regex.charAt(i) == '|' && isOperator(regex, i)) {
                poss.add(regex.substring(start, i));
                start = i + 1;
            }
        }

        if(!poss.isEmpty())
            poss.add(regex.substring(start));

        int leftState = newState(auto);
        int rightState = newState(auto);

        if(!poss.isEmpty())
            for(int i = 0; i < poss.size(); i++) {
                StatePair temp = exchange(poss.get(i), auto);
                auto.transitions.add(new Transition(leftState, temp.left, '$'));
                auto.transitions.add(new Transition(temp.right, rightState, '$'));
            }
        else {
            boolean prefix = false;
            int lastState = leftState;
            for(int i = 0; i < regex.length(); i++) {
                int a, b;
                if(prefix) {
                    //1
                    prefix = false;
                    char transChar;
                    if(regex.charAt(i) == 't')
                        transChar = '\t';
                    else if(regex.charAt(i) == 'n')
                        transChar = '\n';
                    else if(regex.charAt(i) == '_')
                        transChar = ' ';
                    else
                        transChar = regex.charAt(i);
                    a = newState(auto);
                    b = newState(auto);
                    auto.transitions.add(new Transition(a, b, transChar));
                } else {
                    //2
                    if(regex.charAt(i) == '\\') {
                        prefix = true;
                        continue;
                    }
                    if(regex.charAt(i) != '(') {
                        //2a
                        a = newState(auto);
                        b = newState(auto);
                        if(regex.charAt(i) == '$')
                            auto.transitions.add(new Transition(a, b, '$'));
                        else
                            auto.transitions.add(new Transition(a, b, regex.charAt(i)));
                    } else {
                        //2b
                        int j = findMatchingParen(regex, i);
                        StatePair temp = exchange(regex.substring(i + 1, j), auto);
                        a = temp.left;
                        b = temp.right;
                        i = j;
                    }
                }

                if(i + 1 < regex.length() && regex.charAt(i+1) == '*') {
                    int x = a;
                    int y = b;
                    a = newState(auto);
                    b = newState(auto);
                    auto.transitions.add(new Transition(a, x, '$'));
                    auto.transitions.add(new Transition(y, b, '$'));
                    auto.transitions.add(new Transition(a, b, '$'));
                    auto.transitions.add(new Transition(y, x, '$'));
                    i++;
                }

                auto.transitions.add(new Transition(lastState, a, '$'));
                lastState = b;
            }
            auto.transitions.add(new Transition(lastState, rightState, '$'));
        }
        return new StatePair(leftState, rightState);

    }

    public static ArrayList<Automat> sendAutomats() throws IOException {
        BufferedReader br = new BufferedReader(new InputStreamReader(System.in));

        LinkedHashMap<String, String> definitions = new LinkedHashMap<>();
        ArrayList<String> states = new ArrayList<>();
        ArrayList<String> tokens = new ArrayList<>();
        ArrayList<Rule> rules = new ArrayList<>();

        String line;

        Rule currentRule;
        while ((line = br.readLine()) != null) {
            line = line.trim();
            if (line.isEmpty()) continue;

            // 1 Regex
            if (line.startsWith("{")) {
                int end = line.indexOf("}");
                String name = line.substring(1, end);
                String regex = line.substring(end + 1).trim();
                definitions.put(name, regex);
                continue;
            }

            // 2 States
            if (line.startsWith("%X")) {
                String[] parts = line.split("\\s+");
                for (int i = 1; i < parts.length; i++)
                    states.add(parts[i]);
                continue;
            }

            // 3 Tokens
            if (line.startsWith("%L")) {
                String[] parts = line.split("\\s+");
                for (int i = 1; i < parts.length; i++) tokens.add(parts[i]);
                continue;
            }

            // 4 Rules
            if (line.startsWith("<")) {
                currentRule = new Rule();
                int end = line.indexOf(">");
                currentRule.name = line.substring(1, end);
                String reg = line.substring(end + 1).trim();
                currentRule.regex = reg;
                br.readLine();
                while(!(line = br.readLine()).trim().equals("}"))
                    currentRule.actions.add(line.trim());
                rules.add(currentRule);
            }
        }

        boolean changed;

        do {
            changed = false;
            for (Map.Entry<String, String> entry : definitions.entrySet()) {
                String value = entry.getValue();
                if (!containsBracket(value)) continue;

                int start = findFirstOpenBracket(value);
                int end = findFirstClosedBracket(value);
                String newRegex = value.substring(start + 1, end);
                String insert = definitions.get(newRegex);

                String entire = value.substring(0, start) + "(" + insert + ")" + value.substring(end + 1);
                entry.setValue(entire);
                changed = true;
            }
        } while (changed);

        for(Rule r: rules) {
            while(containsBracket(r.regex)) {
                int start = findFirstOpenBracket(r.regex);
                int end = findFirstClosedBracket(r.regex);
                if(end == -1) break;
                if(start == -1) break;
                String newRegex = r.regex.substring(start + 1, end);
                String insert = definitions.get(newRegex);
                r.regex = r.regex.substring(0, start) + "(" + insert + ")" + r.regex.substring(end + 1);
            }
        }
        ArrayList<Automat> tables = new ArrayList<>();
        for(String s: states) {
            Automat auto = new Automat();
            auto.name = s;

            for (Rule r : rules)
                if (r.name.equals(s)) {
                    StatePair pair = new GLA().exchange(r.regex, auto);
                    auto.transitions.add(new Transition(0, pair.left, '$'));
                    auto.acceptable.put(pair.right, r.actions);
                }
            tables.add(auto);
        }
        return tables;
    }


    public static void main(String[] args) {

        try {
            ArrayList<Automat> tables = sendAutomats();

            BufferedWriter writer = new BufferedWriter(new FileWriter("./analizator/automats.txt"));

            for (Automat a : tables) {
                writer.write("Automat: " + a.name);
                writer.newLine();
                writer.write("Acceptable: ");
                writer.newLine();
                for(Map.Entry<Integer, ArrayList<String>> entry : a.acceptable.entrySet()) {
                    writer.write(entry.getKey() + ": ");
                    for(String s : entry.getValue()) {
                        writer.write(s + ", ");
                    }
                    writer.newLine();
                }
                writer.newLine();

                writer.write("Transitions:");
                writer.newLine();

                for (GLA.Transition t : a.transitions) {
                    String symbolStr;
                    switch (t.symbol) {
                        case '\n':
                            symbolStr = "\\n";
                            break;
                        case '\t':
                            symbolStr = "\\t";
                            break;
                        case ' ':
                            symbolStr = "\\_";
                            break;
                        default:
                            symbolStr = String.valueOf(t.symbol);
                            break;
                    }

                    writer.write(t.from + " --" + symbolStr + "--> " + t.to);
                    writer.newLine();
                }
                writer.write("-----");
                writer.newLine();
            }

            writer.close();

        } catch (IOException e) {
            e.printStackTrace();
        }
    }
}
