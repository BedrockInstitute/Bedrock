"""Trilingual syntax help, linked to the project's Agda 2.8 manual.

These are language explanations, not inferred types. Formal blocks use compiler
classification; inline/display snippets use lexical boundaries from the same
version's manual, without treating substrings of identifiers as syntax.
"""
import html
import re
from html.parser import HTMLParser

MANUAL = 'https://agda.readthedocs.io/en/v2.8.0/'
HELP = {}


def entry(keys, page, en, zh, ja):
    for key in keys.split():
        HELP[key] = (MANUAL + page, dict(en=en, zh=zh, ja=ja))


entry('OPTIONS', 'language/pragmas.html', 'Sets checking options for this file.', '指定本文件的检查选项。', 'このファイルの検査オプションを指定する。')
entry('--cubical', 'language/cubical.html', 'Enables cubical type theory, including paths and composition.', '启用立方类型论，包括路径与合成操作。', 'パスと合成を含む立方型理論を有効にする。')
entry('--safe', 'language/safe-agda.html', 'Rejects unsafe features such as unproved postulates and disabled termination checks.', '禁止未证明的公理声明、关闭终止性检查等不安全功能。', '未証明の公理宣言や停止性検査の無効化など、安全でない機能を禁止する。')
entry('--guardedness', 'language/coinduction.html', 'Enables constructor-based guarded corecursion checking.', '启用基于构造子的受保护余递归检查。', '構成子に基づくガード付き余再帰の検査を有効にする。')
entry('module', 'language/module-system.html', 'Declares a namespace, optionally with parameters shared by its definitions.', '声明命名空间，可带由其中定义共享的参数。', '名前空間を宣言する。定義が共有するパラメータも指定できる。')
entry('where', 'language/let-and-where.html', 'Begins a declaration body or the local definitions belonging to a clause.', '开始声明的主体，或某个子句所用的局部定义。', '宣言の本体、または節に属する局所定義を始める。')
entry('open', 'language/module-system.html', 'Makes names from a module available without its qualifier.', '使模块中的名称无需模块前缀即可使用。', 'モジュール内の名前を修飾なしで使えるようにする。')
entry('import', 'language/module-system.html#splitting-a-program-over-multiple-files', 'Loads a module from another file; open import also opens its names.', '从另一文件引入模块；open import 还开放其中的名称。', '別ファイルのモジュールを読み込む。open import は名前も開く。')
entry('using', 'language/module-system.html#name-modifiers', 'Selects the names made available by opening a module.', '选定开放模块时引入的名称。', 'モジュールを開く際に導入する名前を選ぶ。')
entry('hiding', 'language/module-system.html#name-modifiers', 'Excludes listed names when opening a module.', '开放模块时排除列出的名称。', 'モジュールを開く際に列挙した名前を除く。')
entry('renaming to', 'language/module-system.html#name-modifiers', 'Introduces an imported name under a different local name.', '以另一个局部名称引入已有名称。', '既存の名前を別の局所名で導入する。')
entry('as', 'language/module-system.html#splitting-a-program-over-multiple-files', 'Assigns a local alias to an imported module.', '为引入的模块指定局部别名。', '読み込むモジュールに局所的な別名を付ける。')
entry('public', 'language/module-system.html#re-exporting-names', 'Re-exports opened names to clients of this module.', '向本模块的使用者重新导出所开放的名称。', '開いた名前をこのモジュールの利用側へ再公開する。')
entry('private', 'language/module-system.html#private-definitions', 'Keeps declarations inaccessible to importing modules.', '使声明不能被其他模块引入。', '宣言を他のモジュールから参照できなくする。')
entry('data', 'language/data-types.html', 'Defines a datatype by its constructors.', '通过构造子定义数据类型。', '構成子によってデータ型を定義する。')
entry('record', 'language/record-types.html', 'Declares a record type, or constructs a record from field values.', '声明记录类型，或由字段值构造记录。', 'レコード型を宣言するか、フィールドの値からレコードを作る。')
entry('field', 'language/record-types.html', 'Declares the components of a record and their types.', '声明记录的组成字段及其类型。', 'レコードのフィールドとその型を宣言する。')
entry('constructor', 'language/record-types.html', 'Names the constructor of a record.', '为记录的构造子命名。', 'レコードの構成子に名前を付ける。')
entry('inductive coinductive', 'language/record-types.html', 'Specifies inductive or coinductive interpretation of a recursive record.', '指定递归记录采用归纳还是余归纳解释。', '再帰レコードを帰納的に解釈するか余帰納的に解釈するかを指定する。')
entry('eta-equality no-eta-equality', 'language/record-types.html', 'Enables or disables record eta equality.', '启用或禁用记录的 eta 等同性。', 'レコードの eta 等しさを有効または無効にする。')
entry('let in', 'language/let-and-where.html', 'Introduces local definitions used in the expression after in.', '引入在 in 后表达式中使用的局部定义。', 'in の後の式で使う局所定義を導入する。')
entry('λ \\', 'language/lambda-abstraction.html', 'Defines a function by binding its arguments.', '通过绑定参数定义函数。', '引数を束縛して関数を定義する。')
entry('→ -> ∀ forall', 'language/function-types.html', 'Forms a function type; later types may depend on earlier arguments.', '构成函数类型；后续类型可以依赖前面的参数。', '関数型を作る。後の型は先の引数に依存できる。')
entry('with | ...', 'language/with-abstraction.html', 'Splits a definition by inspecting an intermediate expression; vertical bars separate with patterns.', '通过分析中间表达式分情况定义；竖线分隔 with 模式。', '中間の式を調べて場合分けする。縦棒は with のパターンを区切る。')
entry('rewrite', 'language/with-abstraction.html#rewrite', 'Rewrites a goal using an equality before continuing the clause.', '继续子句之前，利用等式改写目标。', '等しさを使って目標を書き換えてから節を続ける。')
entry('opaque unfolding', 'language/opaque-definitions.html', 'Controls which implementation bodies may unfold while checking an opaque block.', '控制检查不透明块时允许展开哪些实现体。', '不透明ブロックの検査時に展開できる定義本体を制御する。')
entry('abstract', 'language/abstract-definitions.html', 'Hides implementation details from reduction outside the abstract scope.', '使抽象作用域外的归约不能使用实现细节。', '抽象的な範囲の外での簡約から実装の詳細を隠す。')
entry('mutual interleaved', 'language/mutual-recursion.html', 'Groups mutually dependent declarations; interleaved permits interleaved signatures and clauses.', '组织相互依赖的声明；interleaved 允许交织签名与子句。', '相互依存する宣言をまとめる。interleaved では型宣言と節を交互に置ける。')
entry('instance overlap', 'language/instance-arguments.html', 'Controls candidates used to solve instance arguments automatically.', '控制自动求解实例参数时使用的候选项。', 'インスタンス引数を自動解決する際の候補を制御する。')
entry('infix infixl infixr', 'language/mixfix-operators.html', 'Sets precedence and non-, left-, or right-associativity of operators.', '指定运算符优先级，以及不结合、左结合或右结合方式。', '演算子の優先順位と、非結合・左結合・右結合を指定する。')
entry('syntax', 'language/syntax-declarations.html', 'Declares concrete notation for an existing definition.', '为已有定义声明具体记法。', '既存の定義に具体的な記法を宣言する。')
entry('pattern', 'language/pattern-synonyms.html', 'Names a reusable pattern.', '为可复用的模式命名。', '再利用できるパターンに名前を付ける。')
entry('variable', 'language/generalization-of-declared-variables.html', 'Declares variables that can be generalized in later signatures.', '声明可在后续签名中被泛化的变量。', '後の型宣言で一般化できる変数を宣言する。')
entry('postulate', 'language/postulates.html', 'Declares a type without a definition; forbidden by this book’s safe mode.', '仅声明类型而不给出定义；本书的安全模式禁止这种做法。', '定義を与えず型を宣言する。本書の安全モードでは禁止される。')
entry('primitive', 'language/built-ins.html', 'Declares a primitive operation implemented by Agda.', '声明由 Agda 实现的原始操作。', 'Agda が実装するプリミティブな操作を宣言する。')
entry('macro quote quoteTerm unquote unquoteDecl unquoteDef tactic', 'language/reflection.html', 'Works with reflected syntax or type-checking computations to inspect or generate terms and declarations.', '通过反射语法或类型检查计算，检查或生成项与声明。', '反映された構文や型検査の計算を用いて、項と宣言を調べたり生成したりする。')
entry('do', 'language/syntactic-sugar.html#do-notation', 'Provides sequential notation expanded into bind operations.', '提供展开为绑定操作的顺序记法。', '束縛操作へ展開される逐次的な記法を提供する。')
entry('=', 'language/function-definitions.html', 'Separates the defining pattern from its value.', '分隔定义的模式与其值。', '定義のパターンとその値を区切る。')
entry(':', 'language/function-types.html', 'Introduces a type annotation for a name or expression.', '为名称或表达式引出类型标注。', '名前や式の型注釈を導入する。')
entry('_', 'language/implicit-arguments.html', 'In an expression, asks Agda to infer a term from context. In a pattern, binder or module declaration, leaves the value, argument or module unnamed.', '在表达式中表示由 Agda 根据上下文推断的占位项；在模式、参数绑定或模块声明中表示不为该值、参数或模块命名。', '式では文脈から Agda が推論する項を表す。パターン・束縛・モジュール宣言では、その値・引数・モジュールに名前を付けないことを表す。')
entry('{ }', 'language/implicit-arguments.html', 'Braces enclose implicit arguments. Depending on the context, they also enclose record fields or pattern-matching lambda clauses. Double braces enclose instance arguments.', '大括号用于包围隐式参数；依语法上下文，也可包围记录字段或模式匹配 λ 的分支。双重大括号用于实例参数。', '波括弧は暗黙の引数を囲む。文脈に応じてレコードのフィールドやパターンマッチ λ の節も囲む。二重の波括弧はインスタンス引数に用いる。')
entry(';', 'language/module-system.html#name-modifiers', 'Separates entries in using, hiding and renaming lists. It also separates record fields or pattern-matching lambda clauses when explicit separators are used.', '分隔 using、hiding、renaming 列表中的项目；也用于显式分隔记录字段或模式匹配 λ 的分支。', 'using・hiding・renaming のリストの項目を区切る。レコードのフィールドやパターンマッチ λ の節を明示的に区切る際にも用いる。')
entry('?', 'language/lexical-structure.html#holes', 'An interactive hole to be filled during development; completed proofs in this book have none.', '开发时待填的交互式空洞；本书完成的证明不含空洞。', '開発中に埋める対話的な穴。本書の完成した証明には残さない。')
entry('..', 'language/irrelevance.html', 'Marks a shape-irrelevant argument.', '标记形状无关的参数。', '形状に関して無関係な引数を示す。')
entry('∀ forall', 'language/function-types.html', 'Binds function arguments whose types Agda infers.', '绑定由 Agda 推断其类型的函数参数。', '型を Agda が推論する関数の引数を束縛する。')
entry('BUILTIN', 'language/built-ins.html', 'Connects a declaration to an entity recognized specially by Agda.', '把声明关联到 Agda 特别识别的内建对象。', '宣言を Agda が特別に認識する組み込み対象に結び付ける。')
entry('COMPILE FOREIGN GHC JS', 'tools/compilers.html', 'Provides backend-specific compilation or foreign-code instructions.', '指定面向编译后端的编译或外部代码指令。', 'コンパイルのバックエンド向けの指示や外部コードを指定する。')
entry('INLINE NOINLINE', 'language/pragmas.html', 'Controls inlining of a definition.', '控制定义的内联展开。', '定義のインライン展開を制御する。')
entry('DISPLAY', 'language/pragmas.html#the-display-pragma', 'Specifies how a term is displayed without changing its meaning.', '指定项的显示方式，不改变其含义。', '意味を変えずに項の表示方法を指定する。')
entry('CATCHALL', 'language/function-definitions.html', 'Marks a catch-all clause for exact-split checking.', '标记精确分割检查中的兜底子句。', '厳密な分割の検査で、残りの場合を扱う節を指定する。')
entry('TERMINATING NON_TERMINATING NO_TERMINATION_CHECK', 'language/termination-checking.html', 'Overrides termination checking; these overrides are not permitted in this book’s safe proofs.', '覆盖终止性检查；本书的安全证明不允许这种覆盖。', '停止性検査を上書きする。本書の安全な証明では許されない。')
entry('NO_POSITIVITY_CHECK NO_UNIVERSE_CHECK NON_COVERING', 'language/safe-agda.html', 'Disables a safety check; not permitted by this book’s safe mode.', '禁用一项安全检查；本书的安全模式不允许使用。', '安全性の検査を無効にする。本書の安全モードでは許されない。')
entry('INJECTIVE INJECTIVE_FOR_INFERENCE', 'language/pragmas.html', 'Controls injectivity assumptions used during unification or type inference.', '控制合一或类型推断时使用的单射性假设。', '単一化や型推論で使う単射性の仮定を制御する。')
entry('NOT_PROJECTION_LIKE', 'language/pragmas.html', 'Disables projection-likeness analysis for a definition.', '禁用某个定义的类投影分析。', '定義が射影に似ているかどうかの解析を無効にする。')
entry('REWRITE', 'language/rewriting.html', 'Registers equations as rewrite rules for reduction.', '把等式注册为归约所用的重写规则。', '等式を簡約で使う書き換え規則として登録する。')
entry('ETA', 'language/record-types.html', 'Enables eta equality for the designated record.', '为指定记录启用 eta 等同性。', '指定したレコードで eta 等しさを有効にする。')
entry('STATIC', 'language/built-ins.html#static-values', 'Marks a definition to be normalized before compilation.', '标记在编译前需要正规化的定义。', 'コンパイル前に正規化する定義を指定する。')
entry('POLARITY', 'language/positivity-checking.html#polarity-pragmas', 'Declares how a postulate uses its arguments for positivity checking; not allowed in safe mode.', '声明公理参数在正性检查中的使用方式；安全模式不允许使用。', '正値性検査のために公理が引数を使う極性を宣言する。安全モードでは許されない。')
entry('WARNING_ON_USAGE WARNING_ON_IMPORT', 'language/pragmas.html', 'Emits a custom warning when the marked name is used or the module is imported.', '使用指定名称或引入指定模块时发出自定义警告。', '指定した名前の使用やモジュールの読み込みに際して独自の警告を出す。')

OPTION_HELP = {
    '--no-sized-types': ('Disables sized types.', '禁用尺寸类型。', 'サイズ付き型を無効にする。'),
    '--no-guardedness': ('Disables constructor-based guarded corecursion.', '禁用基于构造子的受保护余递归。', '構成子に基づくガード付き余再帰を無効にする。'),
    '--cubical-compatible': ('Checks compatibility with cubical mode without enabling its primitives.', '检查与立方模式的兼容性，但不启用其原始操作。', '立方モードのプリミティブを有効にせず、そのモードとの互換性を検査する。'),
    '--level-universe': ('Places universe levels in the dedicated LevelUniv sort.', '把宇宙层级置于专用的 LevelUniv 类中。', '宇宙レベルを専用の LevelUniv ソートに置く。'),
    '--no-exact-split': ('Disables warnings about clauses that are not preserved as definitional equalities.', '禁用针对未保持为定义等式的子句的警告。', '定義による等しさとして保たれない節への警告を無効にする。'),
    '--no-universe-polymorphism': ('Disables universe polymorphism.', '禁用宇宙多态。', '宇宙多相を無効にする。'),
    '--erased-cubical': ('Enables the erased variant of cubical mode.', '启用擦除版本的立方模式。', '立方モードの消去版を有効にする。'),
    '--no-import-sorts': ('Suppresses the implicit import of primitive sorts.', '禁止隐式引入原始类。', 'プリミティブなソートの暗黙のインポートを抑止する。'),
}
for key, descriptions in OPTION_HELP.items():
    entry(key, 'tools/command-line-options.html', *descriptions)


def help_html(key, lang):
    url, text = HELP[key]
    more = dict(en='Learn more', zh='了解更多', ja='詳しく見る')[lang]
    aspect = 'syntax-symbol' if key in SYMBOLS else 'Symbol' if key in PUNCTUATION else 'Keyword'
    return (f'<div class="syntax-help"><strong class="{aspect}">{html.escape(key)}</strong>'
            f'<p>{html.escape(text[lang])}</p><a class="syntax-doc-link" '
            f'href="{html.escape(url, quote=True)}">{more} ↗</a></div>')


RESERVED = frozenset(r'{ } ; _ = | -> → : ? \ λ ∀ .. ... abstract coinductive constructor data do eta-equality field forall hiding import in inductive infix infixl infixr instance interleaved let macro module mutual no-eta-equality opaque open overlap pattern postulate primitive private public quote quoteTerm record renaming rewrite syntax tactic unfolding unquote unquoteDecl unquoteDef using variable where with'.split())
SYMBOLS = frozenset(r'_ = | -> → : ? \ λ ∀ .. ...'.split())
PUNCTUATION = SYMBOLS | frozenset('{};')
INLINE_TOKEN = re.compile(r'"(?:\\.|[^"\\])*"|\'(?:\\[^\s]*?|[^\'\\])\'|[^\s(){};@"]+|.', re.S)


def inline_tokens(code):
    """Reserved whole tokens, never name fragments, quoted text or comments.

    https://agda.readthedocs.io/en/v2.8.0/language/lexical-structure.html
    Qualified/mixfix names stay intact; `to` and `as` need their directive.
    """
    index, comment_depth, pragma = 0, 0, False
    importing, renaming = False, False
    while index < len(code):
        if code.startswith('{-#', index) and not comment_depth:
            pragma = True
            index += 3
            continue
        if code.startswith('#-}', index):
            pragma = False
            index += 3
            continue
        if code.startswith('{-', index):
            comment_depth += 1
            index += 2
            continue
        if comment_depth:
            if code.startswith('-}', index):
                comment_depth -= 1
                index += 2
            else:
                index += 1
            continue
        match = INLINE_TOKEN.match(code, index)
        token = match[0]
        if token.startswith('--') and token not in OPTION_HELP and token not in ('--cubical', '--safe', '--guardedness'):
            newline = code.find('\n', index)
            index = len(code) if newline < 0 else newline + 1
            continue
        keyword = (token in RESERVED or (token == 'as' and importing)
                   or (token == 'to' and renaming) or pragma
                   or token.startswith('--') or (token == code.strip() and token in HELP))
        if token in ('as', 'to'):
            keyword = importing if token == 'as' else renaming
        if not token.startswith(('"', "'")) and not token.isspace():
            yield match.start(), match.end(), token, token in HELP and keyword
        if token == 'import':
            importing = True
        elif token == 'renaming':
            renaming = True
        elif token in ('where', '=', '\n'):
            importing = renaming = False
        index = match.end()


def inline_syntax_ranges(code):
    return ((start, end, token) for start, end, token, syntax in inline_tokens(code) if syntax)


def annotate_inline_code(body, resolve_reference=None):
    """Classify unlinked text in inline code, including single-line displays.

    Read the whole visible snippet before tokenizing, so existing definition
    links cannot break string/comment boundaries. Preserve links and all markup;
    the ordinary annotate_keywords pass supplies the shared hover behavior.
    """
    class InlineSyntax(HTMLParser):
        def __init__(self):
            super().__init__(convert_charrefs=False)
            self.parts, self.stack, self.pending = [], [], []
            self.region = None

        def flush(self):
            if not self.pending:
                return
            raw = ''.join(self.pending)
            self.pending = []
            if self.region is not None:
                decoded = html.unescape(raw)
                start = self.region['length']
                allowed = not any(tag in ('a', 'pre', 'script', 'style', 'template') for tag in self.stack)
                self.region['text'].append(decoded)
                self.region['pieces'].append((len(self.parts), start, decoded, allowed))
                self.region['length'] += len(decoded)
            self.parts.append(raw)

        def finish_region(self):
            region = self.region
            tokens = list(inline_tokens(''.join(region['text'])))
            ranges = []
            for number, (start, end, token, syntax) in enumerate(tokens):
                aspect = 'Symbol' if token in PUNCTUATION else 'Keyword'
                markup = (f'<a class="{aspect}">' + html.escape(token, quote=False) + '</a>'
                          if syntax else resolve_reference(token, tokens, number) if resolve_reference else None)
                if markup:
                    ranges.append((start, end, markup))
            changed = False
            for index, start, decoded, allowed in region['pieces']:
                if not allowed:
                    continue
                hits = [(lo - start, hi - start, markup) for lo, hi, markup in ranges
                        if start <= lo and hi <= start + len(decoded)]
                if not hits:
                    continue
                parts, cursor = [], 0
                for lo, hi, markup in hits:
                    parts.extend((html.escape(decoded[cursor:lo], quote=False),
                                  markup))
                    cursor = hi
                parts.append(html.escape(decoded[cursor:], quote=False))
                self.parts[index] = ''.join(parts)
                changed = True
            if changed and region['tag'] == 'code' and 'Agda' not in region['classes']:
                opening = self.parts[region['opening']]
                if 'class=' in opening:
                    opening = re.sub(r'(class=["\'])', r'\1Agda ', opening, count=1)
                else:
                    opening = opening[:-1] + ' class="Agda">'
                self.parts[region['opening']] = opening
            self.region = None

        def handle_starttag(self, tag, attrs):
            self.flush()
            classes = dict(attrs).get('class', '').split()
            if self.region is None and not any(t in ('pre', 'script', 'style', 'template') for t in self.stack) and (tag == 'code' or tag == 'span' and 'Agda' in classes):
                self.region = dict(text=[], pieces=[], length=0, depth=len(self.stack),
                                   opening=len(self.parts), tag=tag, classes=classes)
            self.parts.append(self.get_starttag_text())
            if tag not in ('area', 'base', 'br', 'col', 'embed', 'hr', 'img', 'input', 'link', 'meta', 'param', 'source', 'track', 'wbr'):
                self.stack.append(tag)

        def handle_endtag(self, tag):
            self.flush()
            if self.stack and self.stack[-1] == tag:
                self.stack.pop()
            if self.region is not None and len(self.stack) == self.region['depth']:
                self.finish_region()
            self.parts.append(f'</{tag}>')

        def handle_startendtag(self, tag, attrs):
            self.flush()
            self.parts.append(self.get_starttag_text())

        def handle_data(self, data):
            self.pending.append(data)

        def handle_entityref(self, name):
            self.pending.append('&' + name + ';')

        def handle_charref(self, name):
            self.pending.append('&#' + name + ';')

        def handle_comment(self, data):
            self.flush()
            self.parts.append('<!--' + data + '-->')

    parser = InlineSyntax()
    parser.feed(body)
    parser.close()
    parser.flush()
    return ''.join(parser.parts)


def annotate_keywords(body, lang):
    # The compiler may group adjacent punctuation, e.g. "(λ" or "→)".
    # Split only non-link Symbol tokens; keep the original source id once.
    def split_symbols(match):
        attrs, content = match.groups()
        cls = re.search(r'class="([^"]*)"', attrs)
        if not cls or 'Symbol' not in cls[1].split() or 'href=' in attrs or 'data-hover-help=' in attrs:
            return match[0]
        decoded = html.unescape(content)
        ranges = list(inline_syntax_ranges(decoded))
        if not ranges or len(ranges) == 1 and ranges[0][:2] == (0, len(decoded)):
            return match[0]
        pieces, cursor = [], 0
        def add(value):
            part_attrs = attrs if not pieces else re.sub(r'\s+id="[^"]*"', '', attrs)
            pieces.append(f'<a{part_attrs}>{html.escape(value, quote=False)}</a>')
        for start, end, _ in ranges:
            if cursor < start:
                add(decoded[cursor:start])
            add(decoded[start:end])
            cursor = end
        if cursor < len(decoded):
            add(decoded[cursor:])
        return ''.join(pieces)
    body = re.sub(r'<a\b([^>]*)>([^<]*)</a>', split_symbols, body)

    def token(match):
        attrs, content = match.groups()
        if 'data-hover-help=' in attrs:
            return match[0]
        cls = re.search(r'class="([^"]*)"', attrs)
        key = html.unescape(content)
        aspects = set(cls[1].split()) if cls else set()
        anonymous = key == '_' and aspects & {'Bound', 'Generalizable', 'Module', 'Function'}
        if not aspects & {'Keyword', 'Symbol', 'Pragma'} and not anonymous:
            return match[0]
        if key not in HELP and 'Keyword' in cls[1].split() and re.fullmatch(r'[A-Z][A-Z0-9_ω-]*', key):
            entry(key, 'language/reflection.html' if key.startswith('AGDA') else 'language/built-ins.html',
                  'A compiler-recognized binding tag used by a BUILTIN pragma, not an ordinary definition.',
                  'BUILTIN 指令使用的编译器内建绑定标记，不是普通定义。',
                  'BUILTIN 指示で使う、コンパイラが認識する束縛タグ。通常の定義ではない。')
        if key not in HELP:
            return match[0]
        cue = ' syntax-hover' + (' syntax-symbol' if key in SYMBOLS else '')
        attrs = re.sub(r'class="([^"]*)"', lambda m: f'class="{m[1]}{cue}"', attrs)
        return (f'<a{attrs} tabindex="0" role="button" aria-haspopup="dialog" '
                f'data-hover-help="{html.escape(key, quote=True)}">{content}</a>')
    return re.sub(r'<a\b([^>]*)>([^<]*)</a>', token, body)
