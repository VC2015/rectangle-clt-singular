-- Keep the Markdown readable on GitHub and the PDF's long identifiers breakable.
local first_title = true

function Header(h)
  if h.level == 1 and first_title then
    first_title = false
    return {}
  end
  h.level = math.max(1, h.level - 1)
  return h
end

function Code(c)
  if FORMAT:match('latex') and not c.text:find('[{}\\]') then
    return pandoc.RawInline('latex', '{\\ttfamily\\nolinkurl{' .. c.text .. '}}')
  end
end

function RawInline(r)
  if FORMAT:match('latex') and r.format == 'html'
      and r.text:match('^<br%s*/?>$') then
    return pandoc.RawInline('latex', '\\newline{}')
  end
end

function Table(t)
  if #t.colspecs == 2 then
    t.colspecs = {{pandoc.AlignLeft, 0.39}, {pandoc.AlignLeft, 0.61}}
  elseif #t.colspecs == 3 then
    t.colspecs = {{pandoc.AlignLeft, 0.16}, {pandoc.AlignLeft, 0.42}, {pandoc.AlignLeft, 0.42}}
  end
  return t
end
