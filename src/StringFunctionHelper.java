import java.util.Arrays;
import java.util.HashSet;

public class StringFunctionHelper {
    public static String sortString(String input) {
        char[] arr = input.toCharArray();
        Arrays.sort(arr);
        return new String(arr);
    }

    public static String convertSetToString(HashSet<Character> set) {
        StringBuilder stringBuilder = new StringBuilder();

        for(Character ch : set) {
            stringBuilder.append(ch);
        }

        return stringBuilder.toString();
    }

    public static Attributes convertStringToAttributes (String str) {
        Attributes att = new Attributes();

        for(int i=0; i<str.length(); i++) {
            att.add(str.charAt(i));
        }

        return att;
    }

    //string contains subCharString => true
    public static boolean stringContainsCharacters(String string, String subCharString) {
        HashSet<Character> set = new HashSet<>();

        char[] stringArr = string.toCharArray();
        for (char c : stringArr) {
            set.add(c);
        }

        char[] subStringArr = subCharString.toCharArray();

        for(char ch: subStringArr) {
            if(!set.contains(ch)) {
                return false;
            }
        }

        return true;
    }
}
