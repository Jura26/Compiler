package SA;
import java.io.BufferedReader;
import java.io.File;
import java.io.IOException;
import java.io.InputStreamReader;
import java.util.ArrayList;
import java.util.Arrays;

public class GSA {
    private static class Production{
        String left;
        ArrayList<String> right = new ArrayList<>();

        Production(String left, ArrayList<String> right){
            this.left = left;
            this.right = right;
        }
        Production(String left,  String right){
            this.left = left;
            this.right.add(right);
        }
    }


    static ArrayList<String> unterminated = new ArrayList<>();
    static ArrayList<String> terminated = new ArrayList<>();
    static ArrayList<String> syncSymb = new ArrayList<>();
    static ArrayList<Production> productions = new ArrayList<>();

    public static void ParseInput() throws IOException {
        BufferedReader br = new BufferedReader(new InputStreamReader(System.in));
        String line;
        Production temp = null;
        while ((line = br.readLine()) != null) {
            if (line.isEmpty()) continue;
            if (line.startsWith("%V")){
                String[] parts = line.split(" ");
                unterminated.addAll(Arrays.asList(parts));
                unterminated.removeFirst();
                continue;
            }
            if (line.startsWith("%T")){
                String[] parts = line.split(" ");
                terminated.addAll(Arrays.asList(parts));
                terminated.removeFirst();
                continue;
            }
            if (line.startsWith("%Syn")){
                String[] parts = line.split(" ");
                syncSymb.addAll(Arrays.asList(parts));
                syncSymb.removeFirst();
                continue;
            }

            if(!line.startsWith(" ")) {
                for (Production production : productions)
                    if (production.left.equals(line))
                        temp = production;

                if (temp == null) {
                    temp = new Production(line, new ArrayList<String>());
                    productions.add(temp);
                }
            } else {

            }

        }

    }

    public static void main(String[] args) {
        try {
            ParseInput();
        }
        catch (IOException e) {
            e.printStackTrace();
        }
        ArrayList<ArrayList<Boolean>> DirectlyStartsWith = new ArrayList<>();

    }
}
