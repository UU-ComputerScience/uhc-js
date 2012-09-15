module Jekyll
  class UHCJSCodeBlock < Liquid::Block
      include Liquid::StandardFilters

      # The regular expression syntax checker. Start with the language specifier.
      # Follow that by zero or more space separated options that take one of two
      # forms:
      #
      # 1. name
      # 2. name=value
      SYNTAX = /^([a-zA-Z0-9.+#-]+)((\s+\w+(=\w+)?)*)$/

      def initialize(tag_name, markup, tokens)
        super
        if markup.strip =~ SYNTAX
          @lang = $1
          if defined?($2) && $2 != ''
            tmp_options = {}
            $2.split.each do |opt|
              key, value = opt.split('=')
              if value.nil?
                if key == 'linenos'
                  value = 'inline'
                else
                  value = true
                end
              end
              tmp_options[key] = value
            end
            tmp_options = tmp_options.to_a.sort.collect { |opt| opt.join('=') }
            # additional options to pass to Albino
            @options = { 'O' => tmp_options.join(',') }
          else
            @options = {}
          end
        else
          raise SyntaxError.new("Syntax Error in 'highlight' - Valid syntax: codeblock <lang> [linenos]")
        end
      end

      def render(context)
        puts super
        "<pre class=\"prettyprint linenums #{@lang.empty? ? '' : 'lang-'+@lang}\">#{h(super).strip}</pre>"
      end
  end
end

Liquid::Template.register_tag('code', Jekyll::UHCJSCodeBlock)